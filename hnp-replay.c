/* Replay one saved HNPFuzzer session through the sock2shm transport,
   without AFL instrumentation or a forkserver. Coverage drivers invoke this
   once per replayable-queue entry so each target session starts from an
   independent process, exactly like the native coverage replay does.

   The delivery loop is afl-fuzz.c's shm path (shm_write/shm_read and the
   send_messages_to_target loop) with the M2 response-copy branch omitted:
   fuzzing keeps sign[8] (is_M2) at 0 outside M2 mutations, so the faithful
   client behavior is the futex barrier, not the data2 copy. */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/shm.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "alloc-inl.h"
#include "sock2shm_utils.h"

#define HR_MAX_MESSAGES 1024
#define HR_CONNECT_TRIES 1000

static msg *hr_session;
static int *hr_netport, *hr_sign;
static int hr_waiting_ms = WAITING_TIME;
static int hr_timed_out;
static volatile sig_atomic_t hr_interrupted;
static pid_t hr_child = -1;
static bool hr_subreaper, hr_segments_removed;
static int hr_msg_id, hr_netport_id, hr_check_id;
static int hr_socket = -1;

static void hr_fail(const char *message) {
  fprintf(stderr, "hnp-replay: %s\n", message);
  exit(1);
}

static void hr_signal(int number) { hr_interrupted = number; }

static uint64_t hr_now_ms(void) {
  struct timespec now;
  if (clock_gettime(CLOCK_MONOTONIC, &now)) hr_fail("clock_gettime failed");
  return (uint64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static unsigned hr_number(const char *text) {
  char *end;
  errno = 0;
  unsigned long value = strtoul(text, &end, 10);
  if (errno || end == text || *end || !value || value > INT_MAX)
    hr_fail("invalid positive integer");
  return (unsigned)value;
}

static void hr_cleanup(void) {
  if (hr_socket >= 0) close(hr_socket);
  if (hr_session) {
    /* Tell a still-running target the session is over, as the fuzzer does. */
    hr_session->is_end = 2;
    shm_notify(&hr_session->state, SERVER);
  }
  if (hr_child > 0) {
    kill(-hr_child, SIGKILL);
    kill(hr_child, SIGKILL);
    while (waitpid(hr_child, NULL, 0) < 0 && errno == EINTR) {}
  }
  if (hr_subreaper) {
    uint64_t deadline = hr_now_ms() + 1000;
    char path[96];
    snprintf(path, sizeof(path), "/proc/self/task/%d/children", getpid());
    do {
      FILE *children = fopen(path, "r");
      if (!children) break;
      int pid;
      while (fscanf(children, "%d", &pid) == 1)
        if (pid > 0) kill(pid, SIGKILL);
      fclose(children);
      pid_t done;
      do { done = waitpid(-1, NULL, WNOHANG); } while (done > 0);
      if (done < 0 && errno == ECHILD) break;
      struct timespec pause = { .tv_nsec = 1000000 };
      nanosleep(&pause, NULL);
    } while (hr_now_ms() < deadline);
  }
  if (!hr_segments_removed) {
    if (hr_msg_id >= 0) shmctl(hr_msg_id, IPC_RMID, NULL);
    if (hr_netport_id >= 0) shmctl(hr_netport_id, IPC_RMID, NULL);
    if (hr_check_id >= 0) shmctl(hr_check_id, IPC_RMID, NULL);
  }
}

/* afl-fuzz.c shm_read() with is_M2 == 0: wait for the target's turn. */
static int hr_shm_read(void) {
  return shm_wait(&hr_session->state, SERVER, hr_waiting_ms) ? 1 : 0;
}

/* afl-fuzz.c shm_write(): len on full delivery, 0 on a timed-out first
   wait, -1 once the target ended the session. */
static int hr_shm_write(const char *mem, unsigned len) {
  int remain, p;
  shm_wait(&hr_session->state, SERVER, hr_waiting_ms);
  if (errno == ETIMEDOUT) return 0;
  if (hr_session->is_end) return -1;
  hr_session->len1 = len;
  for (remain = len, p = 0; remain > 0; ) {
    if (remain < MAX_MSG_SIZE) {
      memcpy(hr_session->data1, mem + p, remain);
      hr_session->buf_size = remain;
      remain = 0;
    } else {
      memcpy(hr_session->data1, mem + p, MAX_MSG_SIZE);
      remain -= MAX_MSG_SIZE;
      hr_session->buf_size = MAX_MSG_SIZE;
      p += MAX_MSG_SIZE;
    }
    do {
      shm_notify(&hr_session->state, SERVER);
      if (shm_wait(&hr_session->state, SERVER, hr_waiting_ms)) {
        hr_session->is_end = 8;
        shm_notify(&hr_session->state, SERVER);
        return -1;
      }
      if (hr_session->is_end) return -1;
    } while (hr_session->buf_size > 0);
  }
  return len;
}

struct hr_message { unsigned char *data; unsigned len; };

static unsigned hr_load_input(const char *path, struct hr_message *messages) {
  FILE *file = fopen(path, "rb");
  struct stat st;
  if (!file || fstat(fileno(file), &st) || !S_ISREG(st.st_mode) ||
      st.st_size <= 0) hr_fail("missing, empty or invalid input");
  size_t size = st.st_size;
  unsigned char *data = malloc(size);
  if (!data || fread(data, 1, size, file) != size) hr_fail("cannot read input");
  fclose(file);
  unsigned count = 0;
  size_t source = 0;
  while (source < size) {
    uint32_t length;
    if (size - source < sizeof(length)) hr_fail("truncated message length");
    memcpy(&length, data + source, sizeof(length));
    source += sizeof(length);
    if (count == HR_MAX_MESSAGES || !length || length > size - source)
      hr_fail("invalid structured message length or count");
    messages[count].data = data + source;
    messages[count].len = length;
    count++;
    source += length;
  }
  if (!count) hr_fail("input has no messages");
  return count;
}

static void hr_set_number(const char *name, int value) {
  char text[32];
  snprintf(text, sizeof(text), "%d", value);
  if (setenv(name, text, 1)) hr_fail("setenv failed");
}

static int hr_connect(int type, unsigned port) {
  struct sockaddr_in address;
  hr_socket = socket(AF_INET, type, 0);
  if (hr_socket < 0) hr_fail("cannot create socket");
  memset(&address, 0, sizeof(address));
  address.sin_family = AF_INET;
  address.sin_port = htons(port);
  address.sin_addr.s_addr = inet_addr("127.0.0.1");
  int n;
  for (n = 0; n < HR_CONNECT_TRIES; n++) {
    if (connect(hr_socket, (struct sockaddr *)&address, sizeof(address)) == 0)
      return 0;
    usleep(1000);
  }
  return 1;
}

int main(int argc, char **argv) {
  const char *input = NULL, *metadata = NULL, *library = NULL, *protocol = "TCP";
  unsigned port = 0, timeout_ms = 10000;
  int option;
  while ((option = getopt(argc, argv, "+i:N:L:t:m:w:h")) != -1) {
    switch (option) {
      case 'i': input = optarg; break;
      case 'N':
        if (!strncmp(optarg, "tcp:", 4)) protocol = "TCP";
        else if (!strncmp(optarg, "udp:", 4)) protocol = "UDP";
        else hr_fail("-N must be tcp:PORT or udp:PORT");
        port = hr_number(optarg + 4);
        break;
      case 'L': library = optarg; break;
      case 't': timeout_ms = hr_number(optarg); break;
      case 'm': metadata = optarg; break;
      case 'w': hr_waiting_ms = (int)hr_number(optarg); break;
      default:
        fprintf(stderr, "Usage: hnp-replay -i input -N tcp:PORT|udp:PORT\n"
                        "  [-L sock2shm.so] [-w futex-wait-ms] [-t timeout-ms]\n"
                        "  [-m metadata.json] -- target [args...]\n");
        return option == 'h' ? 0 : 1;
    }
  }
  if (!input || !port || optind == argc)
    hr_fail("missing arguments; use -h");
  if (getenv(SHM_ENV_MSG_VAR)) hr_fail("nested transport invocation");

  char *preload_library;
  if (library) {
    preload_library = realpath(library, NULL);
  } else {
    char self[PATH_MAX];
    ssize_t length = readlink("/proc/self/exe", self, sizeof(self) - 1);
    if (length <= 0) hr_fail("cannot locate sock2shm.so");
    self[length] = 0;
    char *slash = strrchr(self, '/');
    if (!slash) hr_fail("cannot locate sock2shm.so");
    *slash = 0;
    if (asprintf(&preload_library, "%s/sock2shm.so", self) < 0)
      hr_fail("cannot allocate library path");
  }
  if (!preload_library || access(preload_library, R_OK))
    hr_fail("cannot resolve sock2shm.so; pass -L");

  struct hr_message messages[HR_MAX_MESSAGES];
  unsigned count = hr_load_input(input, messages);
  FILE *metadata_file = NULL;
  if (metadata) {
    metadata_file = fopen(metadata, "wx");
    if (!metadata_file) hr_fail("cannot create metadata output");
  }

  atexit(hr_cleanup);
  hr_msg_id = shmget(IPC_PRIVATE, sizeof(msg), IPC_CREAT | IPC_EXCL | 0600);
  hr_netport_id = shmget(IPC_PRIVATE, sizeof(int), IPC_CREAT | IPC_EXCL | 0600);
  hr_check_id = shmget(IPC_PRIVATE, sizeof(int) * 9, IPC_CREAT | IPC_EXCL | 0600);
  if (hr_msg_id < 0 || hr_netport_id < 0 || hr_check_id < 0)
    hr_fail("shmget failed");
  hr_session = shmat(hr_msg_id, NULL, 0);
  hr_netport = shmat(hr_netport_id, NULL, 0);
  hr_sign = shmat(hr_check_id, NULL, 0);
  if (hr_session == (void *)-1 || !hr_netport || hr_netport == (void *)-1 ||
      !hr_sign || hr_sign == (void *)-1) hr_fail("shmat failed");
  /* Marked for removal while attached: no leak if the driver is killed. */
  shmctl(hr_msg_id, IPC_RMID, NULL);
  shmctl(hr_netport_id, IPC_RMID, NULL);
  shmctl(hr_check_id, IPC_RMID, NULL);
  hr_segments_removed = true;
  memset(hr_session, 0, sizeof(msg));
  memset(hr_sign, 0, sizeof(int) * 9);
  *hr_netport = (int)port;
  /* sign[5..7] exactly as afl-fuzz.c:2506-2509 sets them: terminate_child 0,
     shm transport on, futex synchronization on. is_M2 (sign[8]) stays 0. */
  hr_sign[5] = 0;
  hr_sign[6] = 0;
  hr_sign[7] = 0;
  hr_set_number(SHM_ENV_MSG_VAR, hr_msg_id);
  hr_set_number(SHM_ENV_NETPORT_VAR, hr_netport_id);
  hr_set_number(SHM_ENV_CHECK_VAR, hr_check_id);
  if (setenv(ENV_PROTOCOL_TYPE, protocol, 1)) hr_fail("setenv failed");
  unsetenv("__AFL_SHM_ID");

  const char *previous_preload = getenv("LD_PRELOAD");
  char *preload;
  if (asprintf(&preload, "%s%s%s", preload_library,
               previous_preload && *previous_preload ? ":" : "",
               previous_preload ? previous_preload : "") < 0)
    hr_fail("cannot allocate LD_PRELOAD");
  if (setenv("LD_PRELOAD", preload, 1)) hr_fail("setenv failed");
  free(preload);
  free(preload_library);

  struct sigaction action = { .sa_handler = hr_signal };
  sigemptyset(&action.sa_mask);
  sigaction(SIGINT, &action, NULL);
  sigaction(SIGTERM, &action, NULL);
  if (prctl(PR_SET_CHILD_SUBREAPER, 1)) hr_fail("cannot become child subreaper");
  hr_subreaper = true;

  uint64_t start = hr_now_ms();
  hr_child = fork();
  if (hr_child < 0) hr_fail("fork failed");
  if (!hr_child) {
    if (setpgid(0, 0)) _exit(125);
    if (metadata_file) close(fileno(metadata_file));
    int null_fd = open("/dev/null", O_RDONLY);
    if (null_fd < 0 || dup2(null_fd, STDIN_FILENO) < 0) _exit(125);
    if (null_fd != STDIN_FILENO) close(null_fd);
    execvp(argv[optind], argv + optind);
    perror("hnp-replay: exec");
    _exit(127);
  }
  setpgid(hr_child, hr_child);

  /* The target binds a real socket; connect succeeding is the readiness
     signal, as in the fuzzer's retry loop. */
  int connected = hr_connect(!strcmp(protocol, "UDP") ? SOCK_DGRAM : SOCK_STREAM,
                             port);
  unsigned delivered = 0;
  int status = 0;
  if (!connected) {
    int early = hr_shm_read(); /* wait for the target to enter recv */
    unsigned i;
    for (i = 0; !early && i < count; i++) {
      int written = hr_shm_write((const char *)messages[i].data, messages[i].len);
      if (written == (int)messages[i].len) delivered++;
      if (written != (int)messages[i].len) break;
      early = hr_shm_read();
    }
  }
  if (hr_session) {
    hr_session->is_end = 2;
    shm_notify(&hr_session->state, SERVER);
  }
  if (hr_socket >= 0) { close(hr_socket); hr_socket = -1; }

  bool done = false;
  while (!done) {
    pid_t reaped = waitpid(hr_child, &status, WNOHANG);
    if (reaped == hr_child) done = true;
    else if (reaped < 0 && errno != EINTR) hr_fail("waitpid failed");
    if (hr_interrupted || hr_now_ms() - start >= timeout_ms) {
      hr_timed_out = !hr_interrupted;
      kill(-hr_child, SIGKILL);
      kill(hr_child, SIGKILL);
      while (waitpid(hr_child, &status, 0) < 0 && errno == EINTR) {}
      break;
    }
    if (!done) {
      struct timespec pause = { .tv_nsec = 1000000 };
      nanosleep(&pause, NULL);
    }
  }
  kill(-hr_child, SIGKILL);
  hr_child = -1;
  /* Same adopted-children pass as the engine driver: descendants must not
     keep the coverage profiles or the port for the next input. */
  uint64_t deadline = hr_now_ms() + 1000;
  char path[96];
  snprintf(path, sizeof(path), "/proc/self/task/%d/children", getpid());
  bool cleanup_complete = false;
  for (;;) {
    FILE *children = fopen(path, "r");
    if (!children) { cleanup_complete = true; break; }
    int pid;
    while (fscanf(children, "%d", &pid) == 1)
      if (pid > 0) kill(pid, SIGKILL);
    fclose(children);
    pid_t adopted;
    do { adopted = waitpid(-1, NULL, WNOHANG); } while (adopted > 0);
    if (adopted < 0 && errno == ECHILD) { cleanup_complete = true; break; }
    if (hr_now_ms() >= deadline) break;
    struct timespec pause = { .tv_nsec = 1000000 };
    nanosleep(&pause, NULL);
  }
  int result = hr_interrupted ? 128 + hr_interrupted : hr_timed_out ? 124 :
               WIFSIGNALED(status) ? 128 + WTERMSIG(status) : WEXITSTATUS(status);
  bool started = hr_session && hr_session->is_init;
  if (metadata_file) {
    fprintf(metadata_file,
            "{\"started\":%s,\"messages\":%u,\"messages_delivered\":%u,"
            "\"timed_out\":%s,\"signal\":%d,\"target_exit\":%d,"
            "\"interrupted_signal\":%d,\"cleanup_complete\":%s,"
            "\"elapsed_ms\":%llu,\"result\":%d}\n",
            started ? "true" : "false", count, delivered,
            hr_timed_out ? "true" : "false",
            WIFSIGNALED(status) ? WTERMSIG(status) : 0,
            WIFEXITED(status) ? WEXITSTATUS(status) : -1,
            (int)hr_interrupted, cleanup_complete ? "true" : "false",
            (unsigned long long)(hr_now_ms() - start), result);
    if (fclose(metadata_file)) hr_fail("cannot write metadata");
  }
  fprintf(stderr, "hnp-replay: messages=%u delivered=%u result=%d\n",
          count, delivered, result);
  return result;
}
