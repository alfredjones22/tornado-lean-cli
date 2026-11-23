#ifndef TORNADO_PRIVATE_IO_H
#define TORNADO_PRIVATE_IO_H

#include <lean/lean.h>
#include <stdint.h>

#define TORNADO_MAX_HEX_KEY_FILE 1024u

/* Internal C-only helper. Both output buffers must live in caller-owned
 * protected memory and must be cleared by the caller on every exit path.
 * No key bytes are returned to a Lean object. */
int tornado_private_read_secp256k1_key(
    b_lean_obj_arg path, uint8_t key32[32],
    uint8_t scratch[TORNADO_MAX_HEX_KEY_FILE]);

#endif
