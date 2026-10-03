/* One scheduler process owns its private database volume. */
#include <lean/lean.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <pthread.h>
typedef struct { int fd; } lock_handle;
static void finalize(void *p) { lock_handle *h = p; if (h->fd >= 0) close(h->fd); free(h); }
static void visit(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static lean_external_class *lock_class;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void register_class(void) { lock_class = lean_register_external_class(finalize, visit); }
static lean_obj_res fail(const char *s) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(s)));
}
LEAN_EXPORT lean_obj_res lc_scheduler_lock(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    int fd = open(lean_string_cstr(path), O_CREAT | O_RDWR, 0600);
    if (fd < 0) return fail("Cannot open scheduler lock file");
    fcntl(fd, F_SETFD, FD_CLOEXEC);
    if (flock(fd, LOCK_EX | LOCK_NB)) { close(fd); return fail("Scheduler volume is already in use"); }
    lock_handle *h = malloc(sizeof(*h));
    if (!h) { close(fd); return fail("Scheduler lock allocation failed"); }
    h->fd = fd;
    pthread_once(&once, register_class);
    return lean_io_result_mk_ok(lean_alloc_external(lock_class, h));
}
LEAN_EXPORT lean_obj_res lc_scheduler_unlock(b_lean_obj_arg handle, lean_obj_arg w) {
    (void)w;
    lock_handle *h = lean_get_external_data(handle);
    if (h->fd >= 0) { close(h->fd); h->fd = -1; }
    return lean_io_result_mk_ok(lean_box(0));
}
