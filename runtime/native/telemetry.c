/* Best-effort diagnostics use a separate nonblocking file description.
   A full log pipe drops an observation; it cannot stall a workflow. */
#include <lean/lean.h>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>
#include <errno.h>
#include <time.h>
static int output = -1;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void open_output(void) {
#ifdef __linux__
    output = open("/proc/self/fd/1", O_WRONLY | O_NONBLOCK | O_CLOEXEC);
#else
    output = open("/dev/fd/1", O_WRONLY | O_NONBLOCK | O_CLOEXEC);
#endif
}
LEAN_EXPORT lean_obj_res lc_trace_emit(b_lean_obj_arg text, lean_obj_arg world) {
    (void)world;
    pthread_once(&once, open_output);
    size_t size = lean_string_size(text) - 1;
    /* Fits PIPE_BUF, so a pipe write is atomic or dropped, never interleaved. */
    if (output >= 0 && size <= 2048) {
        sigset_t block, old, pending;
        sigemptyset(&block); sigaddset(&block, SIGPIPE);
        pthread_sigmask(SIG_BLOCK, &block, &old);
        sigpending(&pending);
        int already_pending = sigismember(&pending, SIGPIPE);
        ssize_t result = write(output, lean_string_cstr(text), size);
        if (result < 0 && errno == EPIPE && !already_pending) {
            struct timespec zero = {0};
#ifdef __linux__
            sigtimedwait(&block, NULL, &zero);
#else
            (void)zero;
            sigpending(&pending);
            if (sigismember(&pending, SIGPIPE)) {
                int signal_number;
                sigwait(&block, &signal_number);
            }
#endif
        }
        pthread_sigmask(SIG_SETMASK, &old, NULL);
    }
    return lean_io_result_mk_ok(lean_box(0));
}
