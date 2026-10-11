/* Replace PID 1 with the Lean node. HTTP, SQLite, and the actor run in that
 * process; Docker restarts it after failure. Keep trace writes nonblocking. */
#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#define _DARWIN_C_SOURCE
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <pwd.h>
#include <grp.h>

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "health") == 0) {
        execlp("curl", "curl", "--fail", "--silent", "--max-time", "3",
            "http://127.0.0.1:8080/health", (char *)NULL);
        return 1;
    }
    if (argc < 2) { fputs("cloud-node: expected an application command\n", stderr); return 2; }
    int fd = open("/proc/self/fd/1", O_WRONLY | O_NONBLOCK);
    if (fd >= 0) {
        char value[32]; snprintf(value, sizeof(value), "%d", fd);
        if (setenv("LEAN_CLOUD_TRACE_FD", value, 1) < 0) { close(fd); return 1; }
    }
    if (geteuid() == 0) {
        struct passwd *worker = getpwnam("worker");
        if (!worker || setgroups(0, NULL) || setgid(worker->pw_gid) || setuid(worker->pw_uid)) {
            perror("drop privileges"); return 1;
        }
    }
    char **app = calloc((size_t)argc + 1, sizeof(char *));
    if (!app) return 1;
    app[0] = "cloud-app";
    for (int i = 1; i < argc; ++i) app[i] = argv[i];
    execvp(app[0], app);
    perror("cloud-app"); free(app); return 127;
}
