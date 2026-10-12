#include <lean/lean.h>
#include <signal.h>
#include <errno.h>

/* Lean starts tools with setsid: kill their whole process group on timeout.
   The caller owns and has not yet reaped this child. */
LEAN_EXPORT lean_obj_res lean_sat_kill_group(uint32_t pid, lean_obj_arg world) {
    (void)world;
    if (pid <= 1) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Invalid child PID")));
    if (kill(-(pid_t)pid, SIGKILL) != 0 && errno != ESRCH)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Cannot stop SAT tool process group")));
    return lean_io_result_mk_ok(lean_box(0));
}
