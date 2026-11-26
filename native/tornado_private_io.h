#ifndef TORNADO_PRIVATE_IO_H
#define TORNADO_PRIVATE_IO_H

#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>

#define TORNADO_MAX_HEX_KEY_FILE 1024u

/* Fixed public failure stages only: no path, key bytes, or errno values.
 * This is an internal C contract; no additional Lean FFI is exposed. */
typedef enum {
    TORNADO_KEY_OK = 0,
    TORNADO_KEY_UNKNOWN,
    TORNADO_KEY_PATH_INVALID,
    TORNADO_KEY_PATH_MISSING,
    TORNADO_KEY_PATH_PERMISSION,
    TORNADO_KEY_PATH_NOT_DIRECTORY,
    TORNADO_KEY_PATH_SYMLINK,
    TORNADO_KEY_PATH_UNSAFE,
    TORNADO_KEY_PATH_OPEN,
    TORNADO_KEY_FILE_OPEN,
    TORNADO_KEY_FILE_STAT,
    TORNADO_KEY_FILE_TYPE,
    TORNADO_KEY_FILE_ACL,
    TORNADO_KEY_FILE_OWNER,
    TORNADO_KEY_FILE_LINKS,
    TORNADO_KEY_FILE_MODE,
    TORNADO_KEY_FILE_SIZE,
    TORNADO_KEY_FILE_READ,
    TORNADO_KEY_FILE_UNSTABLE,
    TORNADO_KEY_FILE_CLOSE,
    TORNADO_KEY_FILE_FORMAT,
    TORNADO_KEY_INVALID_SCALAR,
    TORNADO_KEY_CORE_GET,
    TORNADO_KEY_CORE_SET,
    TORNADO_KEY_MEMORY_MAP,
    TORNADO_KEY_MEMORY_LOCK,
    TORNADO_KEY_MEMORY_NODUMP,
    TORNADO_KEY_ENTROPY,
    TORNADO_KEY_CONTEXT_CREATE,
    TORNADO_KEY_CONTEXT_RANDOMIZE,
    TORNADO_KEY_PUBLIC_KEY,
    TORNADO_KEY_SIGN,
    TORNADO_KEY_SIGNATURE_FORMAT,
    TORNADO_KEY_VERIFY,
    TORNADO_KEY_RECOVERY,
    TORNADO_KEY_DIGEST_SIZE,
    TORNADO_KEY_KEYSTORE_SIZE,
    TORNADO_KEY_KEYSTORE_FORMAT,
    TORNADO_KEY_KEYSTORE_UNSUPPORTED,
    TORNADO_KEY_KEYSTORE_BUDGET,
    TORNADO_KEY_KEYSTORE_PASSWORD,
    TORNADO_KEY_KEYSTORE_CRYPTO,
    TORNADO_KEY_KEYSTORE_ADDRESS,
    TORNADO_KEY_KEYSTORE_CHANGED,
    TORNADO_KEY_PASSWORD_FILE,
    TORNADO_KEY_PASSWORD_FORMAT
} tornado_key_status;

/* Internal C-only helper. Both output buffers must live in caller-owned
 * protected memory and must be cleared by the caller on every exit path.
 * No key bytes are returned to a Lean object. */
int tornado_private_read_secp256k1_key(
    b_lean_obj_arg path, uint8_t key32[32],
    uint8_t scratch[TORNADO_MAX_HEX_KEY_FILE], tornado_key_status *status);

/* Protected byte read for native-only key/password handling; never returns a
 * Lean buffer. The caller must supply and clear suitably protected storage. */
typedef struct { uint64_t values[7]; } tornado_key_file_stamp;
int tornado_private_key_material_size(b_lean_obj_arg path, size_t capacity,
    size_t *size, tornado_key_status *status);
int tornado_private_read_key_material(b_lean_obj_arg path,
    uint8_t *scratch, size_t capacity, size_t *size, tornado_key_status *status,
    tornado_key_file_stamp *stamp);

/* C-only helpers for the terminal signer. The input/output buffers remain
 * native; the anchor validation does not create or read a key file. */
int tornado_private_parse_secp256k1_key(const uint8_t *raw, size_t size, uint8_t key32[32]);
int tornado_private_validate_key_anchor(b_lean_obj_arg path);

#endif
