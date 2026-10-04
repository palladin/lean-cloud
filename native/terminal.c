#include <lean/lean.h>
#include <unistd.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <errno.h>

static struct termios saved;
static int active;
static volatile sig_atomic_t interrupted;
static struct sigaction old_int, old_term;
static void stop(int sig) { (void)sig; interrupted = 1; }
static void restore(void) {
    if (!active) return;
    tcsetattr(STDIN_FILENO, TCSANOW, &saved);
    sigaction(SIGINT, &old_int, NULL);
    sigaction(SIGTERM, &old_term, NULL);
    active = 0;
}
LEAN_EXPORT lean_obj_res lc_terminal_enter(lean_obj_arg world) {
    (void)world;
    if (active || !isatty(0) || !isatty(1) || tcgetattr(0, &saved))
        return lean_io_result_mk_ok(lean_box(0));
    struct termios raw = saved;
    raw.c_lflag &= ~(ICANON | ECHO | ISIG);
    raw.c_cc[VMIN] = 0; raw.c_cc[VTIME] = 0;
    if (tcsetattr(0, TCSANOW, &raw)) return lean_io_result_mk_ok(lean_box(0));
    struct sigaction sa = {0}; sa.sa_handler = stop; sigemptyset(&sa.sa_mask);
    sigaction(SIGINT, &sa, &old_int); sigaction(SIGTERM, &sa, &old_term);
    active = 1; interrupted = 0; atexit(restore);
    return lean_io_result_mk_ok(lean_box(1));
}
LEAN_EXPORT lean_obj_res lc_terminal_leave(lean_obj_arg world) {
    (void)world; restore(); return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res lc_terminal_key(uint32_t timeout, lean_obj_arg world) {
    (void)world;
    if (interrupted) return lean_io_result_mk_ok(lean_box_uint32(3));
    struct pollfd p = { .fd = STDIN_FILENO, .events = POLLIN };
    int result = poll(&p, 1, timeout > 60000 ? 60000 : (int)timeout);
    unsigned char ch = 0;
    if (result > 0 && (p.revents & (POLLIN | POLLHUP))) {
        ssize_t count = read(0, &ch, 1);
        if (count == 1) return lean_io_result_mk_ok(lean_box_uint32(ch));
        if (count == 0 || (count < 0 && errno == EIO))
            return lean_io_result_mk_ok(lean_box_uint32(4));
    }
    return lean_io_result_mk_ok(lean_box_uint32(interrupted ? 3 : 0));
}
static unsigned dimension(int cols) {
    struct winsize size;
    if (ioctl(1, TIOCGWINSZ, &size)) return cols ? 100 : 30;
    unsigned value = cols ? size.ws_col : size.ws_row;
    return value ? value : (cols ? 100 : 30);
}
LEAN_EXPORT lean_obj_res lc_terminal_columns(lean_obj_arg w) {
    (void)w; return lean_io_result_mk_ok(lean_box_uint32(dimension(1)));
}
LEAN_EXPORT lean_obj_res lc_terminal_rows(lean_obj_arg w) {
    (void)w; return lean_io_result_mk_ok(lean_box_uint32(dimension(0)));
}
