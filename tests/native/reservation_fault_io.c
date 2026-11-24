/* Test-only process cuts around the actual protected-I/O implementation.
 * This translation unit replaces the production private-I/O object only in
 * the regression binary. No environment switch or hook enters the CLI. */
#define _DARWIN_C_SOURCE 1
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static uint32_t test_fault_mode;
static int test_renamed;
static ssize_t test_write(int fd, const void *buffer, size_t count);
static int test_fsync(int fd);
static int test_renameat(int olddir, const char *oldname, int newdir, const char *newname);

#define write test_write
#define fsync test_fsync
#define renameat test_renameat
#include "../../native/tornado_private_io.c"
#undef write
#undef fsync
#undef renameat

static ssize_t test_write(int fd, const void *buffer, size_t count) {
    if (test_fault_mode == 1 && count > 1) {
        size_t partial = count > 16 ? 16 : 1;
        if (write(fd, buffer, partial) != (ssize_t)partial) _exit(90);
        _exit(81);
    }
    return write(fd, buffer, count);
}

static int test_fsync(int fd) {
    int result = fsync(fd);
    struct stat st;
    if (result == 0 && fstat(fd, &st) == 0) {
        if (test_fault_mode == 2 && S_ISDIR(st.st_mode)) _exit(82);
        if (test_fault_mode == 3 && S_ISREG(st.st_mode)) _exit(83);
        if (test_fault_mode == 4 && test_renamed && S_ISDIR(st.st_mode)) _exit(84);
    }
    return result;
}

static int test_renameat(int olddir, const char *oldname, int newdir, const char *newname) {
    if (test_fault_mode == 5) _exit(85);
    int result = renameat(olddir, oldname, newdir, newname);
    if (result == 0) test_renamed = 1;
    return result;
}

LEAN_EXPORT lean_obj_res tornado_test_fault_arm(uint32_t mode, lean_obj_arg world) {
    (void)world;
    test_renamed = 0;
    test_fault_mode = mode;
    return lean_io_result_mk_ok(lean_box(0));
}
