/*
 * Narrow native secret boundary for funded EOA signing. The protected key
 * file is read into a locked native page, never into a Lean ByteArray.
 * Only an uncompressed public key or public recoverable signature leaves.
 * libsecp256k1 is the pinned v0.8.0 release with the recovery module enabled.
 * OS memory controls and explicit clearing are defense in depth, not a proof
 * that the compiler or libsecp256k1 retains no other transient copies.
 */
#ifndef __APPLE__
#define _GNU_SOURCE 1
#endif
#define _DARWIN_C_SOURCE 1
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>
#include "tornado_private_io.h"
#include "tornado_keystore.h"
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <signal.h>
#include <termios.h>
#include <sys/select.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>

#define TORNADO_SECRET_REGION_BYTES 4096u
#define TORNADO_SECRET_KEY_OFFSET 0u
#define TORNADO_SECRET_SEED_OFFSET 32u
#define TORNADO_SECRET_RAW_OFFSET 64u

#if TORNADO_SECRET_RAW_OFFSET + TORNADO_MAX_HEX_KEY_FILE > TORNADO_SECRET_REGION_BYTES
#error "Secret region is too small for the bounded protected key file"
#endif

static void clear_bytes(void *data, size_t length) {
    volatile uint8_t *bytes = (volatile uint8_t *)data;
    while (length-- > 0) *bytes++ = 0;
}

/* Select only fixed, public stage labels after all sensitive cleanup. */
static const char *failure_message(tornado_key_status status) {
    switch (status) {
    case TORNADO_KEY_PATH_INVALID: return "Protected key path is not a valid absolute file path.";
    case TORNADO_KEY_PATH_MISSING: return "Protected key file is missing. Check the key-file path.";
    case TORNADO_KEY_PATH_PERMISSION: return "Protected key file access was denied. Check file/directory permissions and operating-system folder access.";
    case TORNADO_KEY_PATH_NOT_DIRECTORY: return "Protected key path contains a non-directory or symbolic-link ancestor.";
    case TORNADO_KEY_PATH_SYMLINK: return "Protected key path contains a symbolic link.";
    case TORNADO_KEY_PATH_UNSAFE: return "Protected key path has an unsafe ancestor directory.";
    case TORNADO_KEY_PATH_OPEN: return "Protected key path could not be opened.";
    case TORNADO_KEY_FILE_OPEN: return "Protected key file could not be opened.";
    case TORNADO_KEY_FILE_STAT: return "Protected key file metadata could not be read.";
    case TORNADO_KEY_FILE_TYPE: return "Protected key file must be a regular file.";
    case TORNADO_KEY_FILE_ACL: return "Protected key file ACL policy could not be verified.";
    case TORNADO_KEY_FILE_OWNER: return "Protected key file must be owned by the current user.";
    case TORNADO_KEY_FILE_LINKS: return "Protected key file must have exactly one hard link.";
    case TORNADO_KEY_FILE_MODE: return "Protected key file permissions must exclude group/other access and special bits. Use chmod 600 on the key file.";
    case TORNADO_KEY_FILE_SIZE: return "Protected key file exceeds the 1024-byte limit.";
    case TORNADO_KEY_FILE_READ: return "Protected key file could not be read completely.";
    case TORNADO_KEY_FILE_UNSTABLE: return "Protected key file changed while it was being read.";
    case TORNADO_KEY_FILE_CLOSE: return "Protected key file could not be closed.";
    case TORNADO_KEY_FILE_FORMAT: return "Protected key file must contain one 0x-prefixed 32-byte hex key. Use a raw key file, not an encrypted JSON keystore.";
    case TORNADO_KEY_KEYSTORE_SIZE: return "Encrypted key file exceeds the 64 KiB limit.";
    case TORNADO_KEY_KEYSTORE_FORMAT: return "Malformed encrypted keystore. Use a Web3 Secret Storage v3 account file.";
    case TORNADO_KEY_KEYSTORE_UNSUPPORTED: return "Unsupported keystore format or algorithm. Use v3 with AES-128-CTR and scrypt or PBKDF2-HMAC-SHA256.";
    case TORNADO_KEY_KEYSTORE_BUDGET: return "Keystore KDF parameters exceed the supported resource limits; parameters were not weakened.";
    case TORNADO_KEY_KEYSTORE_PASSWORD: return "Could not decrypt keystore: incorrect password or corrupted file.";
    case TORNADO_KEY_KEYSTORE_CRYPTO: return "Native keystore decryption failed. Check libsodium/OpenSSL availability and the keystore KDF parameters.";
    case TORNADO_KEY_KEYSTORE_ADDRESS: return "Decrypted key does not match the keystore address.";
    case TORNADO_KEY_KEYSTORE_CHANGED: return "Encrypted key file changed after unlocking. Stop and review the original attempt before restarting.";
    case TORNADO_KEY_PASSWORD_FILE: return "Could not read password file. Check its path, ownership, chmod 600, ACLs and 1024-byte limit.";
    case TORNADO_KEY_PASSWORD_FORMAT: return "Password must be at most 1024 UTF-8 bytes without embedded NUL or line breaks.";
    case TORNADO_KEY_INVALID_SCALAR: return "Protected key is not a valid secp256k1 scalar.";
    case TORNADO_KEY_CORE_GET: return "Protected signer could not inspect core-dump limits.";
    case TORNADO_KEY_CORE_SET: return "Protected signer could not disable core dumps.";
    case TORNADO_KEY_MEMORY_MAP: return "Protected signer could not allocate its secret memory region.";
    case TORNADO_KEY_MEMORY_LOCK: return "Protected signer could not lock its secret memory region. Check the process locked-memory limit (ulimit -l).";
    case TORNADO_KEY_MEMORY_NODUMP: return "Protected signer could not exclude its secret memory region from dumps.";
    case TORNADO_KEY_ENTROPY: return "Protected signer could not obtain native entropy.";
    case TORNADO_KEY_CONTEXT_CREATE: return "Protected signer could not allocate the secp256k1 context.";
    case TORNADO_KEY_CONTEXT_RANDOMIZE: return "Protected signer could not randomize the secp256k1 context.";
    case TORNADO_KEY_PUBLIC_KEY: return "Protected signer could not derive the public key.";
    case TORNADO_KEY_SIGN: return "Protected signer could not create a recoverable signature.";
    case TORNADO_KEY_SIGNATURE_FORMAT: return "Protected signer could not serialize a canonical recoverable signature.";
    case TORNADO_KEY_VERIFY: return "Protected signer signature verification failed.";
    case TORNADO_KEY_RECOVERY: return "Protected signer public-key recovery check failed.";
    case TORNADO_KEY_DIGEST_SIZE: return "Protected signer requires an exact 32-byte digest.";
    default: return "Protected native secp256k1 operation failed.";
    }
}

static lean_obj_res fixed_failure(tornado_key_status status) {
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string(failure_message(status))));
}

/* A failure to disable core dumps, pin the page, or exclude it from dumps
 * where supported prevents private-key import. */
static uint8_t *secret_buffer_create(size_t length, tornado_key_status *status) {
    struct rlimit core;
    if (getrlimit(RLIMIT_CORE, &core) != 0) {
        *status = TORNADO_KEY_CORE_GET; return NULL;
    }
    core.rlim_cur = 0;
    core.rlim_max = 0;
    if (setrlimit(RLIMIT_CORE, &core) != 0) {
        *status = TORNADO_KEY_CORE_SET; return NULL;
    }
#ifdef __APPLE__
    const int anon = MAP_ANON;
#else
    const int anon = MAP_ANONYMOUS;
#endif
    void *page = mmap(NULL, length,
        PROT_READ | PROT_WRITE, MAP_PRIVATE | anon, -1, 0);
    if (page == MAP_FAILED) {
        *status = TORNADO_KEY_MEMORY_MAP; return NULL;
    }
    if (mlock(page, length) != 0) {
        *status = TORNADO_KEY_MEMORY_LOCK;
        clear_bytes(page, length);
        munmap(page, length);
        return NULL;
    }
#if defined(MADV_DONTDUMP)
    if (madvise(page, length, MADV_DONTDUMP) != 0) {
        *status = TORNADO_KEY_MEMORY_NODUMP;
        clear_bytes(page, length);
        munlock(page, length);
        munmap(page, length);
        return NULL;
    }
#elif defined(MADV_NOCORE)
    if (madvise(page, length, MADV_NOCORE) != 0) {
        *status = TORNADO_KEY_MEMORY_NODUMP;
        clear_bytes(page, length);
        munlock(page, length);
        munmap(page, length);
        return NULL;
    }
#endif
    return (uint8_t *)page;
}

static uint8_t *secret_region_create(tornado_key_status *status) {
    return secret_buffer_create(TORNADO_SECRET_REGION_BYTES, status);
}

static void secret_buffer_destroy(uint8_t *page, size_t length) {
    if (page == NULL) return;
    clear_bytes(page, length);
    (void)munlock(page, length);
    (void)munmap(page, length);
}

static void secret_region_destroy(uint8_t *page) {
    secret_buffer_destroy(page, TORNADO_SECRET_REGION_BYTES);
}

static int kernel_random32(uint8_t seed[32]) {
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    size_t done = 0;
    while (done < 32) {
        ssize_t n = read(fd, seed + done, 32 - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { close(fd); return 0; }
        done += (size_t)n;
    }
    return close(fd) == 0;
}

/* One command-local interactive key. Only its public, unguessable source
 * alias reaches Lean. It is never written to a file or returned as bytes. */
static uint8_t *interactive_region = NULL;
static char interactive_alias[PATH_MAX];
static int interactive_exit_registered = 0;
static int encrypted_session = 0;
static uint8_t encrypted_fingerprint[32];
static tornado_key_file_stamp encrypted_stamp;
static size_t encrypted_size = 0;
static volatile sig_atomic_t prompt_signal = 0;

static void interactive_clear(void) {
    secret_region_destroy(interactive_region);
    interactive_region = NULL;
    clear_bytes(interactive_alias, sizeof(interactive_alias));
    clear_bytes(encrypted_fingerprint, sizeof(encrypted_fingerprint));
    clear_bytes(&encrypted_stamp, sizeof(encrypted_stamp));
    encrypted_session = 0;
    encrypted_size = 0;
}

static void prompt_interrupted(int signal_number) {
    prompt_signal = signal_number;
}

static lean_obj_res terminal_failure(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/* One bounded, no-echo terminal reader for keys and passwords. The caller's
 * destination is locked. No terminal bytes are copied to Lean or disk. */
static const char *hidden_input(uint8_t *raw, size_t capacity, size_t *used,
    int password) {
    int tty = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
    struct termios before, hidden;
    struct sigaction old_actions[4], action;
    const int signals[4] = { SIGINT, SIGTERM, SIGHUP, SIGQUIT };
    int installed = 0, changed = 0, ok = 0;
    const char *error = password ? "Could not read the keystore password from the controlling terminal."
        : "Could not read the private key from the controlling terminal.";
    *used = 0;
    prompt_signal = 0;
    if (tty < 0 || tty >= FD_SETSIZE || !isatty(tty) || tcgetattr(tty, &before) != 0) {
        error = password ? "No interactive terminal is available. Supply --pwd-file."
            : "No interactive terminal is available. Supply --key-file or --owner-key-file.";
        goto prompt_done;
    }
    memset(&action, 0, sizeof(action));
    action.sa_handler = prompt_interrupted;
    sigemptyset(&action.sa_mask);
    for (; installed < 4; installed++)
        if (sigaction(signals[installed], &action, &old_actions[installed]) != 0)
            goto prompt_done;
    hidden = before;
    hidden.c_lflag &= (tcflag_t)~(ECHO | ECHONL | ICANON);
    hidden.c_cc[VMIN] = 1;
    hidden.c_cc[VTIME] = 0;
    if (tcsetattr(tty, TCSANOW, &hidden) != 0) goto prompt_done;
    changed = 1;
    const char *prompt = password ? "Keystore password (hidden): "
        : "Private key (hidden; 0x followed by 64 hex characters): ";
    if (write(tty, prompt, strlen(prompt)) != (ssize_t)strlen(prompt)) goto prompt_done;
    while (*used <= capacity) {
        if (prompt_signal != 0) goto prompt_done;
        fd_set ready;
        FD_ZERO(&ready);
        FD_SET(tty, &ready);
        struct timeval interval = { 0, 100000 };
        int available = select(tty + 1, &ready, NULL, NULL, &interval);
        if (available < 0 && errno == EINTR) continue;
        if (available < 0) goto prompt_done;
        if (available == 0) continue;
        ssize_t count = read(tty, raw + *used, 1);
        if (count < 0 && errno == EINTR && prompt_signal == 0) continue;
        if (count <= 0 || prompt_signal != 0) goto prompt_done;
        if (raw[*used] == '\n' || raw[*used] == '\r') { ok = 1; break; }
        if (raw[*used] == 4) {
            error = password ? "Keystore password entry was cancelled." : "Private key entry was cancelled.";
            goto prompt_done;
        }
        if (raw[*used] == 8 || raw[*used] == 127) {
            raw[*used] = 0;
            size_t old = *used;
            if (*used > 0) {
                do { --*used; } while (*used > 0 && (raw[*used] & 0xc0u) == 0x80u);
                clear_bytes(raw + *used, old - *used);
            }
            continue;
        }
        if (raw[*used] == 21) {
            clear_bytes(raw, *used + 1);
            *used = 0;
            continue;
        }
        if (*used == capacity) break;
        (*used)++;
    }
    if (!ok) error = password ? "Keystore password input is too long or was cancelled."
        : "Private key input is too long or was cancelled.";
prompt_done:
    if (changed) {
        int flushed, restored;
        do { flushed = tcflush(tty, TCIFLUSH); } while (flushed != 0 && errno == EINTR);
        do { restored = tcsetattr(tty, TCSANOW, &before); } while (restored != 0 && errno == EINTR);
        if (flushed != 0 || restored != 0) {
            ok = 0; error = password ? "Could not restore terminal settings after password entry."
                : "Could not restore terminal settings after private key entry.";
        }
        (void)write(tty, "\n", 1);
    }
    for (int index = installed - 1; index >= 0; index--)
        if (sigaction(signals[index], &old_actions[index], NULL) != 0) {
            ok = 0; error = password ? "Could not restore interrupt handlers after password entry."
                : "Could not restore interrupt handlers after private key entry.";
        }
    if (tty >= 0 && close(tty) != 0) ok = 0;
    if (prompt_signal != 0) {
        ok = 0; error = password ? "Keystore password entry was interrupted." : "Private key entry was interrupted.";
    }
    return ok ? NULL : error;
}

static int register_key_cleanup(void) {
    if (interactive_exit_registered) return 1;
    if (atexit(interactive_clear) != 0) return 0;
    interactive_exit_registered = 1;
    return 1;
}

LEAN_EXPORT lean_obj_res tornado_secure_prompt_key(b_lean_obj_arg anchor,
    lean_obj_arg world) {
    (void)world;
    if (interactive_region != NULL)
        return terminal_failure("An interactive key is already unlocked for this command.");
    if (!tornado_private_validate_key_anchor(anchor))
        return terminal_failure("Interactive signing requires a trusted journal or home directory without symlink ancestors.");
    const char *base = lean_string_cstr(anchor);
    size_t base_length = strlen(base);
    if (base_length + 65 >= sizeof(interactive_alias))
        return terminal_failure("Interactive key source path is too long.");
    tornado_key_status status = TORNADO_KEY_UNKNOWN;
    uint8_t *region = secret_region_create(&status);
    if (region == NULL) return fixed_failure(status);
    uint8_t *raw = region + TORNADO_SECRET_RAW_OFFSET;
    uint8_t *key = region + TORNADO_SECRET_KEY_OFFSET;
    uint8_t *seed = region + TORNADO_SECRET_SEED_OFFSET;
    size_t used;
    const char *error = hidden_input(raw, TORNADO_MAX_HEX_KEY_FILE, &used, 0);
    if (error != NULL) { secret_region_destroy(region); return terminal_failure(error); }
    if (!tornado_private_parse_secp256k1_key(raw, used, key) ||
        !secp256k1_ec_seckey_verify(secp256k1_context_static, key)) {
        secret_region_destroy(region);
        return terminal_failure("Enter one valid Ethereum private key: 0x followed by 64 hex characters.");
    }
    clear_bytes(raw, TORNADO_MAX_HEX_KEY_FILE + 1);
    if (!kernel_random32(seed)) {
        secret_region_destroy(region); return fixed_failure(TORNADO_KEY_ENTROPY);
    }
    memcpy(interactive_alias, base, base_length);
    static const char hex_digits[] = "0123456789abcdef";
    for (size_t index = 0; index < 32; index++) {
        interactive_alias[base_length + 2 * index] = hex_digits[seed[index] >> 4];
        interactive_alias[base_length + 2 * index + 1] = hex_digits[seed[index] & 15];
    }
    interactive_alias[base_length + 64] = '\0';
    clear_bytes(seed, 32);
    if (!register_key_cleanup()) {
        secret_region_destroy(region);
        clear_bytes(interactive_alias, sizeof(interactive_alias));
        return terminal_failure("Could not register interactive signer cleanup.");
    }
    interactive_region = region;
    return lean_io_result_mk_ok(lean_mk_string(interactive_alias));
}

LEAN_EXPORT lean_obj_res tornado_secure_clear_prompt_key(lean_obj_arg world) {
    (void)world;
    interactive_clear();
    return lean_io_result_mk_ok(lean_box(0));
}

/* The size-only probe chooses a bounded allocation; the subsequent independent
 * protected read rechecks its opened inode before/after reading. A race that
 * grows the file beyond the allocation fails rather than reallocating. */
static uint8_t *read_key_source(b_lean_obj_arg path, size_t *allocated,
    size_t *size, tornado_key_file_stamp *stamp, tornado_key_status *status) {
    size_t expected;
    *allocated = 0;
    *size = 0;
    if (!tornado_private_key_material_size(path, TORNADO_MAX_KEYSTORE_FILE, &expected, status)) {
        if (*status == TORNADO_KEY_FILE_SIZE) *status = TORNADO_KEY_KEYSTORE_SIZE;
        return NULL;
    }
    size_t amount = expected == 0 ? 4096 : ((expected + 4095) / 4096) * 4096;
    uint8_t *bytes = secret_buffer_create(amount, status);
    if (bytes == NULL) return NULL;
    if (!tornado_private_read_key_material(path, bytes, amount, size, status, stamp)) {
        if (*status == TORNADO_KEY_FILE_SIZE) *status = TORNADO_KEY_FILE_UNSTABLE;
        secret_buffer_destroy(bytes, amount);
        return NULL;
    }
    *allocated = amount;
    return bytes;
}

static int cached_source_matches(b_lean_obj_arg path, tornado_key_status *status) {
    size_t allocated, size;
    tornado_key_file_stamp stamp;
    uint8_t fingerprint[32];
    uint8_t *bytes = read_key_source(path, &allocated, &size, &stamp, status);
    if (bytes == NULL) return 0;
    int ok = tornado_keystore_fingerprint(bytes, size, fingerprint);
    if (!ok) *status = TORNADO_KEY_KEYSTORE_CRYPTO;
    else if (size != encrypted_size || memcmp(&stamp, &encrypted_stamp, sizeof(stamp)) != 0 ||
             memcmp(fingerprint, encrypted_fingerprint, sizeof(fingerprint)) != 0) {
        *status = TORNADO_KEY_KEYSTORE_CHANGED;
        ok = 0;
    }
    clear_bytes(fingerprint, sizeof(fingerprint));
    clear_bytes(&stamp, sizeof(stamp));
    secret_buffer_destroy(bytes, allocated);
    return ok;
}

static int unlocked_key_valid(uint8_t *region, const tornado_keystore *store,
    tornado_key_status *status) {
    const uint8_t *key = region + TORNADO_SECRET_KEY_OFFSET;
    if (!secp256k1_ec_seckey_verify(secp256k1_context_static, key)) {
        *status = TORNADO_KEY_INVALID_SCALAR; return 0;
    }
    if (!store->has_address) return 1;
    uint8_t *seed = region + TORNADO_SECRET_SEED_OFFSET;
    if (!kernel_random32(seed)) { *status = TORNADO_KEY_ENTROPY; return 0; }
    secp256k1_context *context = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
    if (context == NULL) { *status = TORNADO_KEY_CONTEXT_CREATE; clear_bytes(seed, 32); return 0; }
    int ok = 0;
    secp256k1_pubkey public_key;
    uint8_t serialized[65], digest[32];
    size_t length = sizeof(serialized);
    *status = TORNADO_KEY_CONTEXT_RANDOMIZE;
    if (!secp256k1_context_randomize(context, seed)) goto done;
    *status = TORNADO_KEY_PUBLIC_KEY;
    if (!secp256k1_ec_pubkey_create(context, &public_key, key) ||
        !secp256k1_ec_pubkey_serialize(context, serialized, &length, &public_key,
            SECP256K1_EC_UNCOMPRESSED) || length != 65) goto done;
    *status = TORNADO_KEY_KEYSTORE_CRYPTO;
    if (!tornado_keystore_keccak(serialized + 1, 64, digest)) goto done;
    *status = TORNADO_KEY_KEYSTORE_ADDRESS;
    if (memcmp(digest + 12, store->address, 20) != 0) goto done;
    *status = TORNADO_KEY_OK;
    ok = 1;
done:
    clear_bytes(seed, 32);
    clear_bytes(&public_key, sizeof(public_key));
    clear_bytes(serialized, sizeof(serialized));
    clear_bytes(digest, sizeof(digest));
    secp256k1_context_destroy(context);
    return ok;
}

/* Public arguments select only a source and mode. Password bytes come from a
 * protected native file read or hidden terminal, never from Lean values.
 * mode bit2 = password file supplied; bit4 = prohibit interactive prompting. */
LEAN_EXPORT lean_obj_res tornado_secure_unlock_key_file(b_lean_obj_arg path,
    b_lean_obj_arg password_file, uint32_t mode, lean_obj_arg world) {
    (void)world;
    if ((mode & ~6u) != 0 || (!(mode & 2u) && lean_string_size(password_file) != 1))
        return terminal_failure("Invalid keystore password options. Use --pwd-file or the hidden password prompt.");
    if (interactive_region != NULL)
        return terminal_failure("A key is already unlocked for this command.");
    const char *source = lean_string_cstr(path);
    size_t source_length = lean_string_size(path);
    if (source_length < 2 || source_length > sizeof(interactive_alias) ||
        strlen(source) != source_length - 1)
        return fixed_failure(TORNADO_KEY_PATH_INVALID);
    tornado_key_status status = TORNADO_KEY_UNKNOWN;
    size_t allocated = 0, size = 0;
    tornado_key_file_stamp stamp;
    uint8_t *bytes = read_key_source(path, &allocated, &size, &stamp, &status);
    if (bytes == NULL) return fixed_failure(status);
    uint8_t *region = secret_region_create(&status);
    if (region == NULL) {
        secret_buffer_destroy(bytes, allocated); return fixed_failure(status);
    }
    uint8_t *key = region + TORNADO_SECRET_KEY_OFFSET;
    uint8_t *password = region + 2048;
    uint8_t *work = region + TORNADO_SECRET_RAW_OFFSET;
    size_t password_size = 0, first = 0;
    const char *message = NULL;
    int ok = 0, encrypted = 0;
    tornado_keystore store;
    memset(&store, 0, sizeof(store));
    while (first < size && (bytes[first] == ' ' || bytes[first] == '\t' ||
        bytes[first] == '\r' || bytes[first] == '\n')) first++;
    if (first == size || bytes[first] != '{') {
        status = size > TORNADO_MAX_HEX_KEY_FILE ? TORNADO_KEY_FILE_SIZE : TORNADO_KEY_FILE_FORMAT;
        if (size > TORNADO_MAX_HEX_KEY_FILE ||
            !tornado_private_parse_secp256k1_key(bytes, size, key)) goto done;
        if (mode & 2u) {
            message = "--pwd-file requires an encrypted keystore, not a raw private-key file.";
            goto done;
        }
        if (!secp256k1_ec_seckey_verify(secp256k1_context_static, key)) {
            status = TORNADO_KEY_INVALID_SCALAR; goto done;
        }
        ok = 1;
        goto done;
    }
    if (!tornado_keystore_parse(bytes, size, &store, &status)) goto done;
    if (mode & 2u) {
        if (!tornado_private_read_key_material(password_file, password,
                TORNADO_MAX_PASSWORD + 2, &password_size, &status, NULL)) {
            status = TORNADO_KEY_PASSWORD_FILE; goto done;
        }
        if (password_size > 0 && password[password_size - 1] == '\n') {
            password_size--;
            if (password_size > 0 && password[password_size - 1] == '\r') password_size--;
        }
        if (!tornado_password_valid(password, password_size)) {
            status = TORNADO_KEY_PASSWORD_FORMAT; goto done;
        }
    } else {
        if (mode & 4u) {
            message = "Encrypted key file requires --pwd-file in --non-interactive mode.";
            goto done;
        }
        message = hidden_input(password, TORNADO_MAX_PASSWORD, &password_size, 1);
        if (message != NULL) goto done;
    }
    if (!tornado_keystore_decrypt(&store, password, password_size, key, work, &status) ||
        !unlocked_key_valid(region, &store, &status)) goto done;
    if (!tornado_keystore_fingerprint(bytes, size, encrypted_fingerprint)) {
        status = TORNADO_KEY_KEYSTORE_CRYPTO; goto done;
    }
    if (!register_key_cleanup()) {
        message = "Could not register keystore signer cleanup."; goto done;
    }
    clear_bytes(password, TORNADO_MAX_PASSWORD + 2);
    clear_bytes(work, TORNADO_KEYSTORE_WORK_BYTES);
    memcpy(interactive_alias, source, source_length);
    encrypted_stamp = stamp;
    encrypted_size = size;
    encrypted_session = 1;
    interactive_region = region;
    region = NULL;
    encrypted = 1;
    ok = 1;
done:
    secret_region_destroy(region);
    secret_buffer_destroy(bytes, allocated);
    clear_bytes(&stamp, sizeof(stamp));
    clear_bytes(&store, sizeof(store));
    if (!ok) {
        if (!encrypted) clear_bytes(encrypted_fingerprint, sizeof(encrypted_fingerprint));
        return message != NULL ? terminal_failure(message) : fixed_failure(status);
    }
    return lean_io_result_mk_ok(lean_mk_string(source));
}

/* output is 65 bytes for address derivation and 130 bytes for signing:
 * uncompressed pubkey65 || compact r/s64 || recovery id (only 0 or 1).
 * Signature verification and pubkey recovery bind all three outputs to the
 * exact supplied digest before any result reaches Lean. */
static int with_private_key(b_lean_obj_arg path, const uint8_t *digest32,
    uint8_t *output, int sign, tornado_key_status *status) {
    const size_t output_size = sign ? 130u : 65u;
    uint8_t *region = NULL;
    secp256k1_context *context = NULL;
    int ok = 0;
    *status = TORNADO_KEY_UNKNOWN;
    memset(output, 0, output_size);
    region = secret_region_create(status);
    if (region == NULL) return 0;
    uint8_t *key = region + TORNADO_SECRET_KEY_OFFSET;
    uint8_t *seed = region + TORNADO_SECRET_SEED_OFFSET;
    uint8_t *raw = region + TORNADO_SECRET_RAW_OFFSET;
    if (interactive_region != NULL &&
        strcmp(lean_string_cstr(path), interactive_alias) == 0) {
        if (encrypted_session && !cached_source_matches(path, status)) goto done;
        memcpy(key, interactive_region + TORNADO_SECRET_KEY_OFFSET, 32);
    } else if (!tornado_private_read_secp256k1_key(path, key, raw, status)) goto done;
    if (!kernel_random32(seed)) { *status = TORNADO_KEY_ENTROPY; goto done; }
    context = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
    if (context == NULL) { *status = TORNADO_KEY_CONTEXT_CREATE; goto done; }
    if (!secp256k1_context_randomize(context, seed)) {
        *status = TORNADO_KEY_CONTEXT_RANDOMIZE; goto done;
    }
    if (!secp256k1_ec_seckey_verify(context, key)) {
        *status = TORNADO_KEY_INVALID_SCALAR; goto done;
    }
    secp256k1_pubkey pubkey;
    size_t pubkey_size = 65;
    if (!secp256k1_ec_pubkey_create(context, &pubkey, key) ||
        !secp256k1_ec_pubkey_serialize(context, output, &pubkey_size,
            &pubkey, SECP256K1_EC_UNCOMPRESSED) || pubkey_size != 65) {
        *status = TORNADO_KEY_PUBLIC_KEY; goto done;
    }
    if (sign) {
        secp256k1_ecdsa_recoverable_signature recoverable;
        secp256k1_ecdsa_signature ordinary;
        secp256k1_pubkey recovered;
        uint8_t recovered_bytes[65];
        size_t recovered_size = sizeof(recovered_bytes);
        int recovery_id = -1;
        int signed_ok = 0;
        memset(&recoverable, 0, sizeof(recoverable));
        memset(&ordinary, 0, sizeof(ordinary));
        memset(&recovered, 0, sizeof(recovered));
        memset(recovered_bytes, 0, sizeof(recovered_bytes));
        if (!secp256k1_ecdsa_sign_recoverable(context, &recoverable,
                digest32, key, NULL, NULL)) {
            *status = TORNADO_KEY_SIGN; goto signature_done;
        }
        if (!secp256k1_ecdsa_recoverable_signature_serialize_compact(
                context, output + 65, &recovery_id, &recoverable) ||
            recovery_id < 0 || recovery_id > 1 ||
            !secp256k1_ecdsa_recoverable_signature_convert(context, &ordinary, &recoverable)) {
            *status = TORNADO_KEY_SIGNATURE_FORMAT; goto signature_done;
        }
        if (!secp256k1_ecdsa_verify(context, &ordinary, digest32, &pubkey)) {
            *status = TORNADO_KEY_VERIFY; goto signature_done;
        }
        if (!secp256k1_ecdsa_recover(context, &recovered, &recoverable, digest32) ||
            !secp256k1_ec_pubkey_serialize(context, recovered_bytes,
                &recovered_size, &recovered, SECP256K1_EC_UNCOMPRESSED) ||
            recovered_size != 65 || memcmp(output, recovered_bytes, 65) != 0) {
            *status = TORNADO_KEY_RECOVERY; goto signature_done;
        }
        output[129] = (uint8_t)recovery_id;
        signed_ok = 1;
    signature_done:
        clear_bytes(&recoverable, sizeof(recoverable));
        clear_bytes(&ordinary, sizeof(ordinary));
        clear_bytes(&recovered, sizeof(recovered));
        clear_bytes(recovered_bytes, sizeof(recovered_bytes));
        if (!signed_ok) goto done;
    }
    ok = 1;
    *status = TORNADO_KEY_OK;
done:
    if (!ok) clear_bytes(output, output_size);
    if (context != NULL) secp256k1_context_destroy(context);
    secret_region_destroy(region);
    return ok;
}

LEAN_EXPORT lean_obj_res tornado_secure_pubkey_from_key_file(
    b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    uint8_t output[65];
    tornado_key_status status;
    if (!with_private_key(path, NULL, output, 0, &status)) {
        clear_bytes(output, sizeof(output));
        return fixed_failure(status);
    }
    lean_object *bytes = lean_alloc_sarray(1, sizeof(output), sizeof(output));
    memcpy(lean_sarray_cptr(bytes), output, sizeof(output));
    clear_bytes(output, sizeof(output));
    return lean_io_result_mk_ok(bytes);
}

LEAN_EXPORT lean_obj_res tornado_secure_sign_digest_from_key_file(
    b_lean_obj_arg path, b_lean_obj_arg digest, lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(digest) != 32) return fixed_failure(TORNADO_KEY_DIGEST_SIZE);
    uint8_t output[130];
    tornado_key_status status;
    if (!with_private_key(path, lean_sarray_cptr((lean_object *)digest),
            output, 1, &status)) {
        clear_bytes(output, sizeof(output));
        return fixed_failure(status);
    }
    lean_object *bytes = lean_alloc_sarray(1, sizeof(output), sizeof(output));
    memcpy(lean_sarray_cptr(bytes), output, sizeof(output));
    clear_bytes(output, sizeof(output));
    return lean_io_result_mk_ok(bytes);
}

/* The worker uses Lean-managed experimental note/prover arithmetic. Prevent
 * process core files before it reads any note; this is not memory erasure. */
LEAN_EXPORT lean_obj_res tornado_worker_disable_core_dumps(lean_obj_arg world) {
    (void)world;
    struct rlimit core;
    if (getrlimit(RLIMIT_CORE, &core) != 0) return fixed_failure(TORNADO_KEY_CORE_GET);
    core.rlim_cur = 0;
    core.rlim_max = 0;
    if (setrlimit(RLIMIT_CORE, &core) != 0) return fixed_failure(TORNADO_KEY_CORE_SET);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Only public inputs enter this verifier. Recovery binds the Ethereum v
 * byte as well as r/s to the exact digest and public point. */
LEAN_EXPORT lean_obj_res tornado_verify_public_digest(b_lean_obj_arg public_key,
    b_lean_obj_arg digest, b_lean_obj_arg signature, lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(public_key) != 65 || lean_sarray_size(digest) != 32 ||
        lean_sarray_size(signature) != 65)
        return lean_io_result_mk_ok(lean_box(0));
    const uint8_t *key = lean_sarray_cptr((lean_object *)public_key);
    const uint8_t *msg = lean_sarray_cptr((lean_object *)digest);
    const uint8_t *sig = lean_sarray_cptr((lean_object *)signature);
    if (key[0] != 4 || (sig[64] != 27 && sig[64] != 28))
        return lean_io_result_mk_ok(lean_box(0));
    const secp256k1_context *context = secp256k1_context_static;
    secp256k1_pubkey expected, recovered;
    secp256k1_ecdsa_recoverable_signature recoverable;
    secp256k1_ecdsa_signature ordinary;
    uint8_t recovered_bytes[65];
    size_t recovered_size = sizeof(recovered_bytes);
    int ok = secp256k1_ec_pubkey_parse(context, &expected, key, 65) &&
        secp256k1_ecdsa_recoverable_signature_parse_compact(context,
            &recoverable, sig, (int)sig[64] - 27) &&
        secp256k1_ecdsa_recoverable_signature_convert(context, &ordinary, &recoverable) &&
        secp256k1_ecdsa_verify(context, &ordinary, msg, &expected) &&
        secp256k1_ecdsa_recover(context, &recovered, &recoverable, msg) &&
        secp256k1_ec_pubkey_serialize(context, recovered_bytes, &recovered_size,
            &recovered, SECP256K1_EC_UNCOMPRESSED) && recovered_size == 65 &&
        memcmp(key, recovered_bytes, 65) == 0;
    return lean_io_result_mk_ok(lean_box(ok));
}
