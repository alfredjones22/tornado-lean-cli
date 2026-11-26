#ifndef TORNADO_KEYSTORE_H
#define TORNADO_KEYSTORE_H

#include "tornado_private_io.h"
#include <stddef.h>

#define TORNADO_MAX_KEYSTORE_FILE (64u * 1024u)
#define TORNADO_MAX_PASSWORD 1024u
#define TORNADO_KEYSTORE_WORK_BYTES 1152u

/* Public encrypted parameters only. No password or plaintext key belongs here. */
typedef struct {
    uint8_t ciphertext[32], iv[16], mac[32], salt[1024], address[20];
    size_t salt_size, dklen, ciphertext_size;
    uint64_t n, r, p, iterations;
    int scrypt, has_address;
} tornado_keystore;

int tornado_keystore_parse(const uint8_t *json, size_t size,
    tornado_keystore *result, tornado_key_status *status);
/* Caller supplies locked key/output and work buffers; every exit clears work. */
int tornado_keystore_decrypt(const tornado_keystore *store,
    const uint8_t *password, size_t password_size, uint8_t key32[32],
    uint8_t work[TORNADO_KEYSTORE_WORK_BYTES], tornado_key_status *status);
int tornado_keystore_keccak(const uint8_t *bytes, size_t size, uint8_t hash[32]);
int tornado_keystore_fingerprint(const uint8_t *bytes, size_t size, uint8_t hash[32]);
int tornado_password_valid(const uint8_t *bytes, size_t size);

#endif
