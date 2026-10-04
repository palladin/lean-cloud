/* Owned POSIX process groups with bounded, nonblocking output. No shell parsing. */
#include <lean/lean.h>
#include <spawn.h>
#include <sys/wait.h>
#include <poll.h>
#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <time.h>
#include <stdio.h>

extern char **environ;
typedef struct { pid_t pid; int out, err, reaped, closed; uint32_t code; } process;
static unsigned signal_users;
static volatile sig_atomic_t interrupted;
static struct sigaction previous_int, previous_term;
static void interrupt_process(int sig) { (void)sig; interrupted = 1; }
static void acquire_signals(void) {
    if (signal_users++ != 0) return;
    interrupted = 0;
    struct sigaction action = {0};
    action.sa_handler = interrupt_process; sigemptyset(&action.sa_mask);
    sigaction(SIGINT, &action, &previous_int); sigaction(SIGTERM, &action, &previous_term);
}
static void release_signals(void) {
    if (--signal_users != 0) return;
    sigaction(SIGINT, &previous_int, NULL); sigaction(SIGTERM, &previous_term, NULL);
}

static void close_fd(int *fd) { if (*fd >= 0) { close(*fd); *fd = -1; } }
static void dispose(process *p) {
    if (p->closed) return;
    if (!p->reaped) {
        /* Keep the leader unreaped until group termination: its PID cannot be reused. */
        kill(-p->pid, SIGTERM);
        struct timespec grace = {0, 100000000};
        while (nanosleep(&grace, &grace) < 0 && errno == EINTR) {}
        kill(-p->pid, SIGKILL);
        while (waitpid(p->pid, NULL, 0) < 0 && errno == EINTR) {}
        p->reaped = 1;
    }
    close_fd(&p->out); close_fd(&p->err); p->closed = 1;
    release_signals();
}
static void finalize(void *data) { process *p = data; dispose(p); free(p); }
static void visit(void *data, b_lean_obj_arg f) { (void)data; (void)f; }
static lean_external_class *process_class;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void register_class(void) { process_class = lean_register_external_class(finalize, visit); }
static lean_obj_res fail(const char *operation, int error) {
    char message[256];
    snprintf(message, sizeof(message), "%s: %s", operation, strerror(error));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}
static int make_pipe(int fds[2]) {
    if (pipe(fds)) return errno;
    for (int i = 0; i < 2; ++i) {
        if (fds[i] < 3) {
            int copy = fcntl(fds[i], F_DUPFD, 3);
            if (copy < 0) return errno;
            close(fds[i]); fds[i] = copy;
        }
        if (fcntl(fds[i], F_SETFD, FD_CLOEXEC)) return errno;
    }
    if (fcntl(fds[0], F_SETFL, O_NONBLOCK)) return errno;
    return 0;
}
static int contains_nul(b_lean_obj_arg text) {
    return strlen(lean_string_cstr(text)) != lean_string_size(text) - 1;
}
LEAN_EXPORT lean_obj_res lc_process_start(b_lean_obj_arg command, b_lean_obj_arg args, lean_obj_arg world) {
    (void)world;
    if (contains_nul(command)) return fail("Process argument contains NUL", EINVAL);
    size_t count = lean_array_size(args);
    char **argv = calloc(count + 2, sizeof(char *));
    process *p = calloc(1, sizeof(process));
    if (!argv || !p) { free(argv); free(p); return fail("Allocate process", ENOMEM); }
    argv[0] = (char *)lean_string_cstr(command);
    for (size_t i = 0; i < count; ++i) {
        lean_object *arg = lean_array_get_core(args, i);
        if (contains_nul(arg)) { free(argv); free(p); return fail("Process argument contains NUL", EINVAL); }
        argv[i + 1] = (char *)lean_string_cstr(arg);
    }
    int out[2] = {-1, -1}, err[2] = {-1, -1};
    int error = make_pipe(out);
    if (!error) error = make_pipe(err);
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attr;
    int have_actions = 0, have_attr = 0;
    if (!error) { error = posix_spawn_file_actions_init(&actions); have_actions = !error; }
    if (!error) { error = posix_spawnattr_init(&attr); have_attr = !error; }
#define SETUP(call) do { if (!error) error = (call); } while (0)
    SETUP(posix_spawn_file_actions_addopen(&actions, 0, "/dev/null", O_RDONLY, 0));
    SETUP(posix_spawn_file_actions_adddup2(&actions, out[1], 1));
    SETUP(posix_spawn_file_actions_adddup2(&actions, err[1], 2));
    for (int i = 0; i < 2; ++i) {
        SETUP(posix_spawn_file_actions_addclose(&actions, out[i]));
        SETUP(posix_spawn_file_actions_addclose(&actions, err[i]));
    }
    sigset_t empty, defaults;
    sigemptyset(&empty); sigemptyset(&defaults);
    sigaddset(&defaults, SIGINT); sigaddset(&defaults, SIGTERM);
    sigaddset(&defaults, SIGQUIT); sigaddset(&defaults, SIGPIPE);
    SETUP(posix_spawnattr_setsigmask(&attr, &empty));
    SETUP(posix_spawnattr_setsigdefault(&attr, &defaults));
    SETUP(posix_spawnattr_setpgroup(&attr, 0));
    SETUP(posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP | POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF));
    SETUP(posix_spawnp(&p->pid, argv[0], &actions, &attr, argv, environ));
#undef SETUP
    if (have_attr) posix_spawnattr_destroy(&attr);
    if (have_actions) posix_spawn_file_actions_destroy(&actions);
    free(argv); close_fd(&out[1]); close_fd(&err[1]);
    if (error) { close_fd(&out[0]); close_fd(&err[0]); free(p); return fail("Start process", error); }
    p->out = out[0]; p->err = err[0];
    acquire_signals();
    pthread_once(&once, register_class);
    return lean_io_result_mk_ok(lean_alloc_external(process_class, p));
}
static lean_obj_res read_chunk(int *fd, int *error) {
    unsigned char buffer[8192];
    ssize_t count = *fd < 0 ? 0 : read(*fd, buffer, sizeof(buffer));
    if (!count) close_fd(fd);
    if (count < 0) {
        if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) *error = errno;
        count = 0;
    }
    lean_object *bytes = lean_alloc_sarray(1, (size_t)count, (size_t)count);
    if (count) memcpy(lean_sarray_cptr(bytes), buffer, (size_t)count);
    return bytes;
}
LEAN_EXPORT lean_obj_res lc_process_poll(b_lean_obj_arg handle, uint32_t timeout, lean_obj_arg world) {
    (void)world;
    process *p = lean_get_external_data(handle);
    if (p->closed) return fail("Process is closed", EINVAL);
    if (interrupted) return fail("Process interrupted", EINTR);
    struct pollfd fds[2] = {{p->out, POLLIN, 0}, {p->err, POLLIN, 0}};
    int result = poll(fds, 2, (int)(timeout > 1000 ? 1000 : timeout));
    if (interrupted) return fail("Process interrupted", EINTR);
    if (result < 0 && errno != EINTR) return fail("Poll process", errno);
    int error = 0;
    lean_object *out = read_chunk(&p->out, &error), *err = read_chunk(&p->err, &error);
    if (error) { lean_dec(out); lean_dec(err); return fail("Read process output", error); }
    /* Do not reap the leader early: cancellation must still own its process group. */
    if (!p->reaped && p->out < 0 && p->err < 0) {
        int status;
        pid_t waited = waitpid(p->pid, &status, WNOHANG);
        if (waited < 0 && errno != EINTR) {
            lean_dec(out); lean_dec(err); return fail("Wait for process", errno);
        }
        if (waited == p->pid) {
            p->reaped = 1;
            p->code = WIFEXITED(status) ? (uint32_t)WEXITSTATUS(status) : (uint32_t)(128 + WTERMSIG(status));
        }
    }
    lean_object *code = lean_box(0);
    if (p->reaped) {
        code = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(code, 0, lean_box_uint32(p->code));
    }
    lean_object *chunk = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(chunk, 0, out); lean_ctor_set(chunk, 1, err); lean_ctor_set(chunk, 2, code);
    return lean_io_result_mk_ok(chunk);
}
LEAN_EXPORT lean_obj_res lc_process_close(b_lean_obj_arg handle, lean_obj_arg world) {
    (void)world; dispose(lean_get_external_data(handle)); return lean_io_result_mk_ok(lean_box(0));
}
