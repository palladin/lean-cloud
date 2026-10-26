#include <lean/lean.h>
#include <signal.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>

/* Lean starts tools with setsid: kill their whole process group on timeout.
   The caller owns this command's process group. */
LEAN_EXPORT lean_obj_res lean_cloud_kill_group(uint32_t pid, lean_obj_arg world) {
    (void)world;
    if (pid <= 1) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Invalid child PID")));
    if (kill(-(pid_t)pid, SIGKILL) != 0 && errno != ESRCH) {
        char message[256];
        snprintf(message, sizeof(message), "Cannot stop child process group %u: %s", pid, strerror(errno));
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

#include <sys/stat.h>
LEAN_EXPORT lean_obj_res lean_cloud_file_executable(b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    struct stat info;
    if (stat(lean_string_cstr(path), &info) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Cannot stat artifact")));
    return lean_io_result_mk_ok(lean_box((info.st_mode & 0111) != 0));
}
