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
static uint8_t *secret_region_create(tornado_key_status *status) {
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
    void *page = mmap(NULL, TORNADO_SECRET_REGION_BYTES,
        PROT_READ | PROT_WRITE, MAP_PRIVATE | anon, -1, 0);
    if (page == MAP_FAILED) {
        *status = TORNADO_KEY_MEMORY_MAP; return NULL;
    }
    if (mlock(page, TORNADO_SECRET_REGION_BYTES) != 0) {
        *status = TORNADO_KEY_MEMORY_LOCK;
        clear_bytes(page, TORNADO_SECRET_REGION_BYTES);
        munmap(page, TORNADO_SECRET_REGION_BYTES);
        return NULL;
    }
#if defined(MADV_DONTDUMP)
    if (madvise(page, TORNADO_SECRET_REGION_BYTES, MADV_DONTDUMP) != 0) {
        *status = TORNADO_KEY_MEMORY_NODUMP;
        clear_bytes(page, TORNADO_SECRET_REGION_BYTES);
        munlock(page, TORNADO_SECRET_REGION_BYTES);
        munmap(page, TORNADO_SECRET_REGION_BYTES);
        return NULL;
    }
#elif defined(MADV_NOCORE)
    if (madvise(page, TORNADO_SECRET_REGION_BYTES, MADV_NOCORE) != 0) {
        *status = TORNADO_KEY_MEMORY_NODUMP;
        clear_bytes(page, TORNADO_SECRET_REGION_BYTES);
        munlock(page, TORNADO_SECRET_REGION_BYTES);
        munmap(page, TORNADO_SECRET_REGION_BYTES);
        return NULL;
    }
#endif
    return (uint8_t *)page;
}

static void secret_region_destroy(uint8_t *page) {
    if (page == NULL) return;
    clear_bytes(page, TORNADO_SECRET_REGION_BYTES);
    (void)munlock(page, TORNADO_SECRET_REGION_BYTES);
    (void)munmap(page, TORNADO_SECRET_REGION_BYTES);
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
static volatile sig_atomic_t prompt_signal = 0;

static void interactive_clear(void) {
    secret_region_destroy(interactive_region);
    interactive_region = NULL;
    clear_bytes(interactive_alias, sizeof(interactive_alias));
}

static void prompt_interrupted(int signal_number) {
    prompt_signal = signal_number;
}

static lean_obj_res terminal_failure(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
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
    int tty = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
    struct termios before, hidden;
    struct sigaction old_actions[4], action;
    const int signals[4] = { SIGINT, SIGTERM, SIGHUP, SIGQUIT };
    int installed = 0, changed = 0, ok = 0;
    size_t used = 0;
    const char *error = "Could not read the private key from the controlling terminal.";
    prompt_signal = 0;
    if (tty < 0 || tty >= FD_SETSIZE || !isatty(tty) || tcgetattr(tty, &before) != 0) {
        error = "No interactive terminal is available. Supply --key-file or --owner-key-file.";
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
    const char *prompt = "Private key (hidden; 0x followed by 64 hex characters): ";
    if (write(tty, prompt, strlen(prompt)) != (ssize_t)strlen(prompt)) goto prompt_done;
    while (used < TORNADO_MAX_HEX_KEY_FILE) {
        if (prompt_signal != 0) goto prompt_done;
        fd_set ready;
        FD_ZERO(&ready);
        FD_SET(tty, &ready);
        struct timeval interval = { 0, 100000 };
        int available = select(tty + 1, &ready, NULL, NULL, &interval);
        if (available < 0 && errno == EINTR) continue;
        if (available < 0) goto prompt_done;
        if (available == 0) continue;
        ssize_t count = read(tty, raw + used, 1);
        if (count < 0 && errno == EINTR && prompt_signal == 0) continue;
        if (count <= 0 || prompt_signal != 0) goto prompt_done;
        if (raw[used] == '\n' || raw[used] == '\r') { ok = 1; break; }
        if (raw[used] == 4) { error = "Private key entry was cancelled."; goto prompt_done; }
        if (raw[used] == 8 || raw[used] == 127) {
            raw[used] = 0;
            if (used > 0) raw[--used] = 0;
            continue;
        }
        if (raw[used] == 21) {
            clear_bytes(raw, used + 1);
            used = 0;
            continue;
        }
        used++;
    }
    if (!ok) error = "Private key input is too long or was cancelled.";
prompt_done:
    if (changed) {
        /* Discard pasted typeahead so it cannot approve a later SEND prompt. */
        int flushed, restored;
        do { flushed = tcflush(tty, TCIFLUSH); } while (flushed != 0 && errno == EINTR);
        do { restored = tcsetattr(tty, TCSANOW, &before); } while (restored != 0 && errno == EINTR);
        if (flushed != 0 || restored != 0) {
            ok = 0; error = "Could not restore terminal settings after private key entry.";
        }
        (void)write(tty, "\n", 1);
    }
    for (int index = installed - 1; index >= 0; index--)
        if (sigaction(signals[index], &old_actions[index], NULL) != 0) {
            ok = 0; error = "Could not restore interrupt handlers after private key entry.";
        }
    if (tty >= 0 && close(tty) != 0) ok = 0;
    if (prompt_signal != 0) { ok = 0; error = "Private key entry was interrupted."; }
    if (!ok) { secret_region_destroy(region); return terminal_failure(error); }
    if (!tornado_private_parse_secp256k1_key(raw, used, key) ||
        !secp256k1_ec_seckey_verify(secp256k1_context_static, key)) {
        secret_region_destroy(region);
        return terminal_failure("Enter one valid Ethereum private key: 0x followed by 64 hex characters.");
    }
    clear_bytes(raw, TORNADO_MAX_HEX_KEY_FILE);
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
    if (!interactive_exit_registered && atexit(interactive_clear) != 0) {
        secret_region_destroy(region);
        clear_bytes(interactive_alias, sizeof(interactive_alias));
        return terminal_failure("Could not register interactive signer cleanup.");
    }
    interactive_exit_registered = 1;
    interactive_region = region;
    return lean_io_result_mk_ok(lean_mk_string(interactive_alias));
}

LEAN_EXPORT lean_obj_res tornado_secure_clear_prompt_key(lean_obj_arg world) {
    (void)world;
    interactive_clear();
    return lean_io_result_mk_ok(lean_box(0));
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
