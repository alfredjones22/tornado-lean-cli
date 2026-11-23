/*
 * Trusted OS boundary for private Tornado files. No protocol, cryptography,
 * JSON, networking, or wallet decisions live here. POSIX/macOS and Linux only.
 * Paths must be absolute and every ancestor must be a trusted real directory.
 */
#define _DARWIN_C_SOURCE 1
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include "tornado_private_io.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#ifdef __APPLE__
#include <sys/acl.h>
#endif

#ifndef O_CLOEXEC
#error "O_CLOEXEC is required for private file operations"
#endif
#ifndef O_NOFOLLOW
#error "O_NOFOLLOW is required for private file operations"
#endif
#ifndef O_DIRECTORY
#error "O_DIRECTORY is required for private file operations"
#endif

#define TORNADO_MAX_PRIVATE_FILE (1024u * 1024u)

/* Best-effort clearing for temporary native buffers. This does not erase
 * copies already held by Lean values or successful read results. */
static void clear_bytes(void *data, size_t length) {
    volatile uint8_t *bytes = (volatile uint8_t *)data;
    while (length-- > 0) *bytes++ = 0;
}

/* macOS ACL grants are independent of mode bits and can be inherited by a
 * newly created 0600 file. Deny-only ACLs (for example the home directory's
 * default deny-delete entry) cannot grant access. Inspect the opened inode. */
static int no_acl_grants(int fd) {
#ifdef __APPLE__
    int previous_errno = errno;
    acl_t acl = acl_get_fd_np(fd, ACL_TYPE_EXTENDED);
    if (acl == NULL) {
        if (errno != ENOENT) return 0;
        errno = previous_errno; /* no extended ACL */
        return 1;
    }
    if (acl_valid(acl) != 0) {
        int saved = errno;
        acl_free(acl);
        errno = saved;
        return 0;
    }
    acl_entry_t entry;
    int index = ACL_FIRST_ENTRY;
    while (acl_get_entry(acl, index, &entry) == 0) {
        acl_tag_t tag;
        if (acl_get_tag_type(entry, &tag) != 0) {
            int saved = errno;
            acl_free(acl);
            errno = saved;
            return 0;
        }
        if (tag != ACL_EXTENDED_DENY) {
            acl_free(acl);
            errno = EPERM;
            return 0;
        }
        index = ACL_NEXT_ENTRY;
    }
    int saved = errno;
    acl_free(acl);
    if (saved != EINVAL) { errno = saved; return 0; }
    errno = previous_errno;
#else
    (void)fd;
#endif
    return 1;
}

#ifdef __APPLE__
#define ST_MTIME_NSEC(st) ((st).st_mtimespec.tv_nsec)
#define ST_CTIME_NSEC(st) ((st).st_ctimespec.tv_nsec)
#else
#define ST_MTIME_NSEC(st) ((st).st_mtim.tv_nsec)
#define ST_CTIME_NSEC(st) ((st).st_ctim.tv_nsec)
#endif

static lean_obj_res failure(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

static lean_obj_res failure_errno(const char *operation) {
    char message[160];
    int e = errno;
    (void)snprintf(message, sizeof(message), "Private file %s failed (errno %d)", operation, e);
    return failure(message);
}

static int trusted_dir(int fd) {
    struct stat st;
    if (fstat(fd, &st) != 0) return 0;
    return S_ISDIR(st.st_mode) && no_acl_grants(fd) &&
           (st.st_uid == 0 || st.st_uid == geteuid()) &&
           (st.st_mode & (S_IWGRP | S_IWOTH)) == 0;
}

/* Walk with directory descriptors, so a symlink cannot redirect any ancestor. */
static int private_parent(b_lean_obj_arg path_obj, char basename[NAME_MAX + 1]) {
    const char *path = lean_string_cstr(path_obj);
    size_t length = lean_string_size(path_obj);
    if (length < 3 || length > PATH_MAX || path[0] != '/' ||
        strlen(path) != length - 1 || path[length - 2] == '/') {
        errno = EINVAL;
        return -1;
    }
    int dir = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dir < 0) return -1;
    if (!trusted_dir(dir)) { close(dir); errno = EPERM; return -1; }
    size_t start = 1;
    for (size_t pos = 1; pos <= length - 1; pos++) {
        if (path[pos] != '/' && path[pos] != '\0') continue;
        size_t n = pos - start;
        if (n == 0 || n > NAME_MAX ||
            (n == 2 && path[start] == '.' && path[start + 1] == '.')) {
            close(dir); errno = EINVAL; return -1;
        }
        if (n == 1 && path[start] == '.') {
            if (path[pos] == '\0') { close(dir); errno = EINVAL; return -1; }
            start = pos + 1;
            continue;
        }
        char name[NAME_MAX + 1];
        memcpy(name, path + start, n);
        name[n] = '\0';
        if (path[pos] == '\0') {
            memcpy(basename, name, n + 1);
            return dir;
        }
        int next = openat(dir, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (next < 0) { close(dir); return -1; }
        close(dir);
        dir = next;
        if (!trusted_dir(dir)) { close(dir); errno = EPERM; return -1; }
        start = pos + 1;
    }
    close(dir);
    errno = EINVAL;
    return -1;
}

static int private_regular(int fd, struct stat *st) {
    if (fstat(fd, st) != 0) return 0;
    if (!S_ISREG(st->st_mode) || !no_acl_grants(fd) ||
        st->st_uid != geteuid() ||
        st->st_nlink != 1 || (st->st_mode & 077) != 0 ||
        (st->st_mode & (S_ISUID | S_ISGID | S_ISVTX)) != 0) {
        errno = EPERM;
        return 0;
    }
    return 1;
}

/* Byte-level equivalent of Domain.jsWhitespace / PrivateKeyInput.parse.
 * Whitespace varies only outside the fixed 64 secret hex digits. */
static size_t hex_key_whitespace_at(const uint8_t *raw, size_t size, size_t i) {
    if (i >= size) return 0;
    unsigned int a = raw[i];
    if ((a >= 9 && a <= 13) || a == 0x20) return 1;
    if (i + 2 <= size && a == 0xc2 && raw[i + 1] == 0xa0) return 2;
    if (i + 3 > size) return 0;
    unsigned int b = raw[i + 1], c = raw[i + 2];
    if (a == 0xe1 && b == 0x9a && c == 0x80) return 3;
    if (a == 0xe2 && b == 0x80 &&
        ((c >= 0x80 && c <= 0x8a) || c == 0xa8 || c == 0xa9 || c == 0xaf))
        return 3;
    if (a == 0xe2 && b == 0x81 && c == 0x9f) return 3;
    if (a == 0xe3 && b == 0x80 && c == 0x80) return 3;
    if (a == 0xef && b == 0xbb && c == 0xbf) return 3;
    return 0;
}

static size_t hex_key_whitespace_before(
    const uint8_t *raw, size_t size, size_t end) {
    if (end >= 3 && hex_key_whitespace_at(raw, size, end - 3) == 3) return 3;
    if (end >= 2 && hex_key_whitespace_at(raw, size, end - 2) == 2) return 2;
    if (end >= 1 && hex_key_whitespace_at(raw, size, end - 1) == 1) return 1;
    return 0;
}

/* Fixed-length, branch-free-with-respect-to-nibble-class hex conversion.
 * The compiler output is still part of the native side-channel audit. */
static uint32_t hex_key_nibble(uint8_t value, uint32_t *valid) {
    uint32_t digit = (uint32_t)value - (uint32_t)'0';
    uint32_t alpha = ((uint32_t)value | 0x20u) - (uint32_t)'a';
    uint32_t is_digit = (uint32_t)(digit <= 9u);
    uint32_t is_alpha = (uint32_t)(alpha <= 5u);
    *valid &= is_digit | is_alpha;
    return (digit & (0u - is_digit)) | ((alpha + 10u) & (0u - is_alpha));
}

static int parse_hex_key(const uint8_t *raw, size_t size, uint8_t key32[32]) {
    size_t start = 0, stop = size;
    while (start < size) {
        size_t skip = hex_key_whitespace_at(raw, size, start);
        if (skip == 0) break;
        start += skip;
    }
    while (stop > start) {
        size_t skip = hex_key_whitespace_before(raw, size, stop);
        if (skip == 0) break;
        stop -= skip;
    }
    if (stop - start != 66 || raw[start] != '0' || raw[start + 1] != 'x')
        return 0;
    uint32_t valid = 1;
    for (size_t i = 0; i < 32; i++) {
        uint32_t hi = hex_key_nibble(raw[start + 2 + 2 * i], &valid);
        uint32_t lo = hex_key_nibble(raw[start + 3 + 2 * i], &valid);
        key32[i] = (uint8_t)((hi << 4) | lo);
    }
    return valid == 1;
}

/* Read a protected key directly into caller-owned native memory. This uses
 * the same descriptor walk, inode checks, size/mtime/ctime recheck and ACL
 * policy as readPrivate. The bridge owns clearing scratch and key32. */
int tornado_private_read_secp256k1_key(
    b_lean_obj_arg path, uint8_t key32[32],
    uint8_t scratch[TORNADO_MAX_HEX_KEY_FILE]) {
    if (key32 == NULL || scratch == NULL) return 0;
    char name[NAME_MAX + 1];
    int dir = private_parent(path, name);
    if (dir < 0) return 0;
    int fd = openat(dir, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    close(dir);
    if (fd < 0) return 0;
    struct stat before, after;
    if (!private_regular(fd, &before) || before.st_size < 0 ||
        before.st_size > TORNADO_MAX_HEX_KEY_FILE) {
        close(fd);
        return 0;
    }
    size_t size = (size_t)before.st_size;
    size_t done = 0;
    while (done < size) {
        ssize_t n = read(fd, scratch + done, size - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { close(fd); return 0; }
        done += (size_t)n;
    }
    int stable = private_regular(fd, &after) &&
                 before.st_dev == after.st_dev && before.st_ino == after.st_ino &&
                 before.st_size == after.st_size &&
                 before.st_mtime == after.st_mtime &&
                 before.st_ctime == after.st_ctime &&
                 ST_MTIME_NSEC(before) == ST_MTIME_NSEC(after) &&
                 ST_CTIME_NSEC(before) == ST_CTIME_NSEC(after);
    if (close(fd) != 0) stable = 0;
    return stable && parse_hex_key(scratch, size, key32);
}

/* Verify a final directory by inode, after private_parent has walked every
 * ancestor without following symlinks. Claims use nullifier-derived names,
 * so only the current account may be able to list this directory. */
LEAN_EXPORT lean_obj_res tornado_private_dir_check(
    b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    char name[NAME_MAX + 1];
    int parent = private_parent(path, name);
    if (parent < 0) return failure_errno("directory path validation");
    int fd = openat(parent, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) { close(parent); return failure_errno("directory open"); }
    struct stat st;
    int good = fstat(fd, &st) == 0 && S_ISDIR(st.st_mode) &&
               st.st_uid == geteuid() && (st.st_mode & 07777) == 0700 &&
               no_acl_grants(fd);
    if (close(fd) != 0) good = 0;
    close(parent);
    if (!good) return failure("Private directory must be owner-only mode 0700 without ACL grants");
    return lean_io_result_mk_ok(lean_box(0));
}

static int write_all(int fd, b_lean_obj_arg data_obj) {
    size_t length = lean_sarray_size(data_obj);
    const uint8_t *data = lean_sarray_cptr((lean_object *)data_obj);
    size_t done = 0;
    while (done < length) {
        ssize_t n = write(fd, data + done, length - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        done += (size_t)n;
    }
    return 0;
}

/* Compare the opened protected inode with the caller's exact prior bytes.
 * The sidecar lock serializes all cooperating writers of this journal. */
static int original_matches(int fd, b_lean_obj_arg expected, struct stat *before) {
    size_t length = lean_sarray_size(expected);
    if (!private_regular(fd, before) || before->st_size < 0 ||
        (uint64_t)before->st_size != length) {
        errno = EAGAIN;
        return 0;
    }
    const uint8_t *prior = lean_sarray_cptr((lean_object *)expected);
    uint8_t chunk[8192];
    size_t offset = 0;
    while (offset < length) {
        size_t wanted = length - offset < sizeof(chunk) ? length - offset : sizeof(chunk);
        ssize_t count = read(fd, chunk, wanted);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0 || memcmp(chunk, prior + offset, (size_t)count) != 0) {
            clear_bytes(chunk, sizeof(chunk));
            errno = EAGAIN;
            return 0;
        }
        offset += (size_t)count;
    }
    struct stat after;
    if (!private_regular(fd, &after) || before->st_dev != after.st_dev ||
        before->st_ino != after.st_ino || before->st_size != after.st_size ||
        before->st_mtime != after.st_mtime || before->st_ctime != after.st_ctime ||
        ST_MTIME_NSEC(*before) != ST_MTIME_NSEC(after) ||
        ST_CTIME_NSEC(*before) != ST_CTIME_NSEC(after)) {
        clear_bytes(chunk, sizeof(chunk));
        errno = EAGAIN;
        return 0;
    }
    clear_bytes(chunk, sizeof(chunk));
    return 1;
}

static int same_named_inode(int dir, const char *name, const struct stat *opened) {
    struct stat current;
    return fstatat(dir, name, &current, AT_SYMLINK_NOFOLLOW) == 0 &&
           S_ISREG(current.st_mode) && current.st_dev == opened->st_dev &&
           current.st_ino == opened->st_ino && current.st_nlink == 1;
}

static int random_temp_name(char out[64]) {
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    uint8_t random[16];
    size_t done = 0;
    while (done < sizeof(random)) {
        ssize_t n = read(fd, random + done, sizeof(random) - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { close(fd); return 0; }
        done += (size_t)n;
    }
    if (close(fd) != 0) return 0;
    static const char hex[] = "0123456789abcdef";
    memcpy(out, ".tornado-replace-", 17);
    for (size_t i = 0; i < sizeof(random); i++) {
        out[17 + i * 2] = hex[random[i] >> 4];
        out[18 + i * 2] = hex[random[i] & 15];
    }
    memcpy(out + 49, ".tmp", 5);
    return 1;
}

/* Atomic compare-and-replace of an existing private file. A per-file O_EXCL
 * sidecar lock is held until the new inode and parent directory are synced.
 * A crash may leave this lock behind; callers must inspect before removing it.
 * A post-rename sync failure has an ambiguous durability outcome and must be
 * reported separately from a pre-rename failure. */
LEAN_EXPORT lean_obj_res tornado_private_replace(
    b_lean_obj_arg path, b_lean_obj_arg expected, b_lean_obj_arg data,
    lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(expected) > TORNADO_MAX_PRIVATE_FILE ||
        lean_sarray_size(data) > TORNADO_MAX_PRIVATE_FILE)
        return failure("Private file exceeds the 1 MiB limit");
    char name[NAME_MAX + 1];
    int dir = private_parent(path, name);
    if (dir < 0) return failure_errno("replacement path validation");
    char lock_name[NAME_MAX + 1];
    int lock_length = snprintf(lock_name, sizeof(lock_name), ".%s.tornado-lock", name);
    if (lock_length < 0 || (size_t)lock_length >= sizeof(lock_name)) {
        close(dir);
        return failure("Private file name is too long for its replacement lock");
    }
    int lock_fd = openat(dir, lock_name,
        O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (lock_fd < 0) { close(dir); return failure_errno("replacement lock create"); }
    struct stat lock_stat;
    int have_lock_inode = fstat(lock_fd, &lock_stat) == 0;
    int lock_ok = have_lock_inode && fchmod(lock_fd, 0600) == 0 &&
                  private_regular(lock_fd, &lock_stat) && fsync(lock_fd) == 0;
    if (close(lock_fd) != 0) lock_ok = 0;
    if (!lock_ok) {
        int saved = errno;
        if (have_lock_inode && same_named_inode(dir, lock_name, &lock_stat))
            (void)unlinkat(dir, lock_name, 0);
        close(dir); errno = saved;
        return failure_errno("replacement lock validation");
    }
    int original = -1, temp = -1, temp_created = 0, have_temp_inode = 0;
    char temp_name[64] = { 0 };
    struct stat original_stat, temp_stat;
    const char *failure_stage = "compare-and-replace before rename";
    original = openat(dir, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (original < 0 || !original_matches(original, expected, &original_stat))
        goto pre_rename_failure;
    if (!random_temp_name(temp_name)) goto pre_rename_failure;
    temp = openat(dir, temp_name,
        O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (temp < 0) goto pre_rename_failure;
    temp_created = 1;
    if (fstat(temp, &temp_stat) != 0) goto pre_rename_failure;
    have_temp_inode = 1;
    if (fchmod(temp, 0600) != 0 || !private_regular(temp, &temp_stat) ||
        write_all(temp, data) != 0 || !private_regular(temp, &temp_stat) ||
        fsync(temp) != 0) goto pre_rename_failure;
    if (close(temp) != 0) { temp = -1; goto pre_rename_failure; }
    temp = -1;
    if (!same_named_inode(dir, name, &original_stat) ||
        !same_named_inode(dir, temp_name, &temp_stat)) {
        errno = EAGAIN;
        goto pre_rename_failure;
    }
    if (renameat(dir, temp_name, dir, name) != 0) goto pre_rename_failure;
    temp_created = 0;
    if (close(original) != 0) {
        original = -1;
        failure_stage = "replaced journal, but original close failed; inspect it before retrying";
        goto post_rename_failure;
    }
    original = -1;
    if (fsync(dir) != 0) {
        failure_stage = "replaced journal, but parent sync failed; inspect it before retrying";
        goto post_rename_failure;
    }
    if (!same_named_inode(dir, lock_name, &lock_stat) ||
        unlinkat(dir, lock_name, 0) != 0 || fsync(dir) != 0) {
        failure_stage = "journal replaced and synced, but lock cleanup failed";
        goto post_rename_failure;
    }
    close(dir);
    return lean_io_result_mk_ok(lean_box(0));

pre_rename_failure: {
    int saved = errno;
    if (temp >= 0) (void)close(temp);
    if (temp_created && have_temp_inode && same_named_inode(dir, temp_name, &temp_stat))
        (void)unlinkat(dir, temp_name, 0);
    if (original >= 0) (void)close(original);
    if (same_named_inode(dir, lock_name, &lock_stat))
        (void)unlinkat(dir, lock_name, 0);
    (void)fsync(dir);
    close(dir); errno = saved;
    return failure_errno(failure_stage);
}
post_rename_failure:
    if (original >= 0) (void)close(original);
    close(dir);
    return failure(failure_stage);
}

/* Remove only the exact protected file bytes the caller created. Used to
 * release a successful sender lock; a changed lock must remain in place. */
LEAN_EXPORT lean_obj_res tornado_private_remove_exact(
    b_lean_obj_arg path, b_lean_obj_arg expected, lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(expected) > TORNADO_MAX_PRIVATE_FILE)
        return failure("Private file exceeds the 1 MiB limit");
    char name[NAME_MAX + 1];
    int dir = private_parent(path, name);
    if (dir < 0) return failure_errno("remove path validation");
    int fd = openat(dir, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) { close(dir); return failure_errno("remove open"); }
    struct stat st;
    if (!original_matches(fd, expected, &st) ||
        !same_named_inode(dir, name, &st)) {
        close(fd); close(dir);
        return failure("Private file changed before exact removal");
    }
    if (unlinkat(dir, name, 0) != 0) {
        int saved = errno;
        close(fd); close(dir); errno = saved;
        return failure_errno("exact removal");
    }
    int synced = fsync(dir) == 0;
    int closed = close(fd) == 0;
    if (close(dir) != 0) closed = 0;
    if (!synced || !closed)
        return failure("Private file was removed, but durability or close failed; inspect before retrying");
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res tornado_private_create(
    b_lean_obj_arg path, b_lean_obj_arg data, lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(data) > TORNADO_MAX_PRIVATE_FILE)
        return failure("Private file exceeds the 1 MiB limit");
    char name[NAME_MAX + 1];
    int dir = private_parent(path, name);
    if (dir < 0) return failure_errno("path validation");
    int fd = openat(dir, name, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd < 0) { close(dir); return failure_errno("exclusive create"); }
    struct stat st;
    int have_inode = fstat(fd, &st) == 0;
    int good = have_inode && fchmod(fd, 0600) == 0 && private_regular(fd, &st) &&
               write_all(fd, data) == 0 && private_regular(fd, &st) && fsync(fd) == 0;
    int saved = errno;
    if (close(fd) != 0) good = 0;
    if (!good) {
        struct stat current;
        if (have_inode && fstatat(dir, name, &current, AT_SYMLINK_NOFOLLOW) == 0 &&
            current.st_dev == st.st_dev && current.st_ino == st.st_ino)
            (void)unlinkat(dir, name, 0);
        close(dir);
        errno = saved;
        return failure_errno("write and sync");
    }
    if (fsync(dir) != 0) { close(dir); return failure_errno("directory sync"); }
    close(dir);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res tornado_private_read(
    b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    char name[NAME_MAX + 1];
    int dir = private_parent(path, name);
    if (dir < 0) return failure_errno("path validation");
    int fd = openat(dir, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) { close(dir); return failure_errno("open"); }
    struct stat before, after;
    if (!private_regular(fd, &before) || before.st_size < 0 ||
        before.st_size > TORNADO_MAX_PRIVATE_FILE) {
        close(fd); close(dir); return failure("Private file has unsafe metadata or size");
    }
    size_t size = (size_t)before.st_size;
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    uint8_t *buffer = lean_sarray_cptr(bytes);
    size_t done = 0;
    while (done < size) {
        ssize_t n = read(fd, buffer + done, size - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) {
            clear_bytes(buffer, size);
            lean_dec(bytes); close(fd); close(dir);
            return failure("Private file changed during read");
        }
        done += (size_t)n;
    }
    int stable = private_regular(fd, &after) &&
                 before.st_dev == after.st_dev && before.st_ino == after.st_ino &&
                 before.st_size == after.st_size &&
                 before.st_mtime == after.st_mtime &&
                 before.st_ctime == after.st_ctime &&
                 ST_MTIME_NSEC(before) == ST_MTIME_NSEC(after) &&
                 ST_CTIME_NSEC(before) == ST_CTIME_NSEC(after);
    if (close(fd) != 0) stable = 0;
    close(dir);
    if (!stable) {
        clear_bytes(buffer, size);
        lean_dec(bytes);
        return failure("Private file changed during read");
    }
    return lean_io_result_mk_ok(bytes);
}
