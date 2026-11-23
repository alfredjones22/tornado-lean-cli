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

static lean_obj_res fixed_failure(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("Protected native secp256k1 operation failed.")));
}

/* A failure to disable core dumps, pin the page, or exclude it from dumps
 * where supported prevents private-key import. */
static uint8_t *secret_region_create(void) {
    struct rlimit core;
    if (getrlimit(RLIMIT_CORE, &core) != 0) return NULL;
    core.rlim_cur = 0;
    core.rlim_max = 0;
    if (setrlimit(RLIMIT_CORE, &core) != 0) return NULL;
#ifdef __APPLE__
    const int anon = MAP_ANON;
#else
    const int anon = MAP_ANONYMOUS;
#endif
    void *page = mmap(NULL, TORNADO_SECRET_REGION_BYTES,
        PROT_READ | PROT_WRITE, MAP_PRIVATE | anon, -1, 0);
    if (page == MAP_FAILED) return NULL;
    if (mlock(page, TORNADO_SECRET_REGION_BYTES) != 0) {
        munmap(page, TORNADO_SECRET_REGION_BYTES);
        return NULL;
    }
#if defined(MADV_DONTDUMP)
    if (madvise(page, TORNADO_SECRET_REGION_BYTES, MADV_DONTDUMP) != 0) {
        clear_bytes(page, TORNADO_SECRET_REGION_BYTES);
        munlock(page, TORNADO_SECRET_REGION_BYTES);
        munmap(page, TORNADO_SECRET_REGION_BYTES);
        return NULL;
    }
#elif defined(MADV_NOCORE)
    if (madvise(page, TORNADO_SECRET_REGION_BYTES, MADV_NOCORE) != 0) {
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

/* output is 65 bytes for address derivation and 130 bytes for signing:
 * uncompressed pubkey65 || compact r/s64 || recovery id (only 0 or 1).
 * Signature verification and pubkey recovery bind all three outputs to the
 * exact supplied digest before any result reaches Lean. */
static int with_private_key(b_lean_obj_arg path, const uint8_t *digest32,
    uint8_t *output, int sign) {
    const size_t output_size = sign ? 130u : 65u;
    uint8_t *region = NULL;
    secp256k1_context *context = NULL;
    int ok = 0;
    memset(output, 0, output_size);
    region = secret_region_create();
    if (region == NULL) return 0;
    uint8_t *key = region + TORNADO_SECRET_KEY_OFFSET;
    uint8_t *seed = region + TORNADO_SECRET_SEED_OFFSET;
    uint8_t *raw = region + TORNADO_SECRET_RAW_OFFSET;
    if (!tornado_private_read_secp256k1_key(path, key, raw) ||
        !kernel_random32(seed)) goto done;
    context = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
    if (context == NULL || !secp256k1_context_randomize(context, seed) ||
        !secp256k1_ec_seckey_verify(context, key)) goto done;
    secp256k1_pubkey pubkey;
    size_t pubkey_size = 65;
    if (!secp256k1_ec_pubkey_create(context, &pubkey, key) ||
        !secp256k1_ec_pubkey_serialize(context, output, &pubkey_size,
            &pubkey, SECP256K1_EC_UNCOMPRESSED) || pubkey_size != 65)
        goto done;
    if (sign) {
        secp256k1_ecdsa_recoverable_signature recoverable;
        secp256k1_ecdsa_signature ordinary;
        secp256k1_pubkey recovered;
        uint8_t recovered_bytes[65];
        size_t recovered_size = sizeof(recovered_bytes);
        int recovery_id = -1;
        memset(&recoverable, 0, sizeof(recoverable));
        memset(&ordinary, 0, sizeof(ordinary));
        memset(&recovered, 0, sizeof(recovered));
        if (!secp256k1_ecdsa_sign_recoverable(context, &recoverable,
                digest32, key, NULL, NULL) ||
            !secp256k1_ecdsa_recoverable_signature_serialize_compact(
                context, output + 65, &recovery_id, &recoverable) ||
            recovery_id < 0 || recovery_id > 1 ||
            !secp256k1_ecdsa_recoverable_signature_convert(
                context, &ordinary, &recoverable) ||
            !secp256k1_ecdsa_verify(context, &ordinary, digest32, &pubkey) ||
            !secp256k1_ecdsa_recover(context, &recovered, &recoverable, digest32) ||
            !secp256k1_ec_pubkey_serialize(context, recovered_bytes,
                &recovered_size, &recovered, SECP256K1_EC_UNCOMPRESSED) ||
            recovered_size != 65 || memcmp(output, recovered_bytes, 65) != 0) {
            clear_bytes(&recoverable, sizeof(recoverable));
            clear_bytes(&ordinary, sizeof(ordinary));
            clear_bytes(&recovered, sizeof(recovered));
            clear_bytes(recovered_bytes, sizeof(recovered_bytes));
            goto done;
        }
        output[129] = (uint8_t)recovery_id;
        clear_bytes(&recoverable, sizeof(recoverable));
        clear_bytes(&ordinary, sizeof(ordinary));
        clear_bytes(&recovered, sizeof(recovered));
        clear_bytes(recovered_bytes, sizeof(recovered_bytes));
    }
    ok = 1;
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
    if (!with_private_key(path, NULL, output, 0)) {
        clear_bytes(output, sizeof(output));
        return fixed_failure();
    }
    lean_object *bytes = lean_alloc_sarray(1, sizeof(output), sizeof(output));
    memcpy(lean_sarray_cptr(bytes), output, sizeof(output));
    clear_bytes(output, sizeof(output));
    return lean_io_result_mk_ok(bytes);
}

LEAN_EXPORT lean_obj_res tornado_secure_sign_digest_from_key_file(
    b_lean_obj_arg path, b_lean_obj_arg digest, lean_obj_arg world) {
    (void)world;
    if (lean_sarray_size(digest) != 32) return fixed_failure();
    uint8_t output[130];
    if (!with_private_key(path, lean_sarray_cptr((lean_object *)digest),
            output, 1)) {
        clear_bytes(output, sizeof(output));
        return fixed_failure();
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
    if (getrlimit(RLIMIT_CORE, &core) != 0) return fixed_failure();
    core.rlim_cur = 0;
    core.rlim_max = 0;
    if (setrlimit(RLIMIT_CORE, &core) != 0) return fixed_failure();
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
