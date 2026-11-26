/* Web3 Secret Storage v3 parsing/decryption. Crypto uses OpenSSL/libcrypto
 * and libsodium's low-level scrypt for historical geth parameter compatibility;
 * this module implements no cipher, KDF or hash primitive. See root LICENSE.
 * Parsing is bounded, rejects duplicates and accepts canonical ASCII keys.
 * Unknown metadata is parsed but never interpreted as executable behavior. */
#include "tornado_keystore.h"
#include <openssl/evp.h>
#include <openssl/crypto.h>
#include <sodium.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>

enum json_kind { J_OBJECT, J_ARRAY, J_STRING, J_NUMBER, J_LITERAL };
typedef struct { size_t start, end, next; enum json_kind kind; } token;
typedef struct {
    const uint8_t *data;
    size_t size, position, count;
    token tokens[512];
} json_parser;

static void wipe(void *data, size_t size) { OPENSSL_cleanse(data, size); }
static int hex_digit(uint8_t c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* Reject overlong encodings, surrogate scalars and code points > U+10FFFF. */
static int utf8(const uint8_t *bytes, size_t size) {
    size_t i = 0;
    while (i < size) {
        uint8_t c = bytes[i++];
        if (c < 0x80) continue;
        size_t remaining;
        uint32_t value, minimum;
        if (c >= 0xc2 && c <= 0xdf) { remaining = 1; value = c & 31u; minimum = 0x80; }
        else if (c >= 0xe0 && c <= 0xef) { remaining = 2; value = c & 15u; minimum = 0x800; }
        else if (c >= 0xf0 && c <= 0xf4) { remaining = 3; value = c & 7u; minimum = 0x10000; }
        else return 0;
        if (remaining > size - i) return 0;
        for (size_t j = 0; j < remaining; j++) {
            uint8_t d = bytes[i++];
            if ((d & 0xc0u) != 0x80u) return 0;
            value = (value << 6) | (d & 63u);
        }
        if (value < minimum || value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff)) return 0;
    }
    return 1;
}

int tornado_password_valid(const uint8_t *bytes, size_t size) {
    if (size > TORNADO_MAX_PASSWORD || !utf8(bytes, size)) return 0;
    for (size_t i = 0; i < size; i++)
        if (bytes[i] == 0 || bytes[i] == '\n' || bytes[i] == '\r') return 0;
    return 1;
}

static void whitespace(json_parser *p) {
    while (p->position < p->size) {
        uint8_t c = p->data[p->position];
        if (c != ' ' && c != '\n' && c != '\r' && c != '\t') return;
        p->position++;
    }
}
static int unicode_escape(json_parser *p, unsigned *value) {
    if (p->size - p->position < 4) return 0;
    unsigned n = 0;
    for (size_t j = 0; j < 4; j++) {
        int h = hex_digit(p->data[p->position++]);
        if (h < 0) return 0;
        n = (n << 4) | (unsigned)h;
    }
    *value = n;
    return 1;
}
static int string_token(json_parser *p, size_t t, int key) {
    if (p->position >= p->size || p->data[p->position++] != '"') return 0;
    p->tokens[t].start = p->position;
    while (p->position < p->size) {
        uint8_t c = p->data[p->position++];
        if (c == '"') {
            p->tokens[t].end = p->position - 1;
            return 1;
        }
        if (c < 0x20) return 0;
        if (key && (c == '\\' || c >= 0x80)) return 0;
        if (c != '\\') continue;
        if (p->position >= p->size) return 0;
        c = p->data[p->position++];
        if (c == 'u') {
            unsigned value;
            if (!unicode_escape(p, &value)) return 0;
            if (value >= 0xd800 && value <= 0xdbff) {
                if (p->size - p->position < 2 || p->data[p->position++] != '\\' ||
                    p->data[p->position++] != 'u') return 0;
                if (!unicode_escape(p, &value) || value < 0xdc00 || value > 0xdfff) return 0;
            } else if (value >= 0xdc00 && value <= 0xdfff) return 0;
        } else if (c != '"' && c != '\\' && c != '/' && c != 'b' &&
                   c != 'f' && c != 'n' && c != 'r' && c != 't') return 0;
    }
    return 0;
}
static int token_equal(json_parser *p, size_t a, size_t b) {
    token x = p->tokens[a], y = p->tokens[b];
    return x.end - x.start == y.end - y.start &&
        memcmp(p->data + x.start, p->data + y.start, x.end - x.start) == 0;
}
static int value(json_parser *p, size_t depth, size_t *result) {
    if (depth > 32 || p->count >= 512) return 0;
    whitespace(p);
    if (p->position >= p->size) return 0;
    size_t t = p->count++;
    *result = t;
    p->tokens[t].start = p->position;
    uint8_t c = p->data[p->position];
    if (c == '{' || c == '[') {
        int object = c == '{';
        p->tokens[t].kind = object ? J_OBJECT : J_ARRAY;
        p->position++;
        whitespace(p);
        uint8_t close = object ? '}' : ']';
        if (p->position < p->size && p->data[p->position] == close) p->position++;
        else for (;;) {
            if (object) {
                if (p->count >= 512) return 0;
                size_t k = p->count++;
                p->tokens[k].kind = J_STRING;
                if (!string_token(p, k, 1)) return 0;
                p->tokens[k].next = p->count;
                for (size_t previous = t + 1; previous < k;) {
                    if (token_equal(p, previous, k)) return 0;
                    previous = p->tokens[previous + 1].next;
                }
                whitespace(p);
                if (p->position >= p->size || p->data[p->position++] != ':') return 0;
            }
            size_t child;
            if (!value(p, depth + 1, &child)) return 0;
            whitespace(p);
            if (p->position >= p->size) return 0;
            c = p->data[p->position++];
            if (c == close) break;
            if (c != ',') return 0;
            whitespace(p);
        }
        p->tokens[t].end = p->position;
    } else if (c == '"') {
        p->tokens[t].kind = J_STRING;
        if (!string_token(p, t, 0)) return 0;
    } else if (c == '-' || (c >= '0' && c <= '9')) {
        p->tokens[t].kind = J_NUMBER;
        if (c == '-') p->position++;
        if (p->position >= p->size) return 0;
        c = p->data[p->position++];
        if (c == '0') {
            if (p->position < p->size && p->data[p->position] >= '0' && p->data[p->position] <= '9') return 0;
        } else {
            if (c < '1' || c > '9') return 0;
            while (p->position < p->size && p->data[p->position] >= '0' && p->data[p->position] <= '9') p->position++;
        }
        if (p->position < p->size && p->data[p->position] == '.') {
            p->position++;
            size_t start = p->position;
            while (p->position < p->size && p->data[p->position] >= '0' && p->data[p->position] <= '9') p->position++;
            if (p->position == start) return 0;
        }
        if (p->position < p->size && (p->data[p->position] == 'e' || p->data[p->position] == 'E')) {
            p->position++;
            if (p->position < p->size && (p->data[p->position] == '+' || p->data[p->position] == '-')) p->position++;
            size_t start = p->position;
            while (p->position < p->size && p->data[p->position] >= '0' && p->data[p->position] <= '9') p->position++;
            if (p->position == start) return 0;
        }
        p->tokens[t].end = p->position;
    } else {
        p->tokens[t].kind = J_LITERAL;
        const char *literal = c == 't' ? "true" : c == 'f' ? "false" : c == 'n' ? "null" : "";
        size_t n = strlen(literal);
        if (n == 0 || n > p->size - p->position || memcmp(p->data + p->position, literal, n) != 0) return 0;
        p->position += n;
        p->tokens[t].end = p->position;
    }
    p->tokens[t].next = p->count;
    return 1;
}

static int equals(json_parser *p, int t, const char *text) {
    if (t < 0 || p->tokens[t].kind != J_STRING) return 0;
    token x = p->tokens[t];
    return strlen(text) == x.end - x.start && memcmp(p->data + x.start, text, x.end - x.start) == 0;
}
static int field(json_parser *p, int object, const char *name) {
    if (object < 0 || p->tokens[object].kind != J_OBJECT) return -1;
    for (size_t i = (size_t)object + 1; i < p->tokens[object].next;) {
        if (equals(p, (int)i, name)) return (int)i + 1;
        i = p->tokens[i + 1].next;
    }
    return -1;
}
static int integer(json_parser *p, int t, uint64_t *result) {
    if (t < 0 || p->tokens[t].kind != J_NUMBER) return 0;
    token x = p->tokens[t];
    uint64_t n = 0;
    for (size_t i = x.start; i < x.end; i++) {
        uint8_t c = p->data[i];
        if (c < '0' || c > '9' || n > (UINT64_MAX - (uint64_t)(c - '0')) / 10) return 0;
        n = n * 10 + (uint64_t)(c - '0');
    }
    *result = n;
    return 1;
}
static int hex_bytes(json_parser *p, int t, uint8_t *out, size_t min, size_t max, size_t *size) {
    if (t < 0 || p->tokens[t].kind != J_STRING) return 0;
    token x = p->tokens[t];
    size_t n = x.end - x.start;
    if (n % 2 || n / 2 < min || n / 2 > max) return 0;
    for (size_t j = 0; j < n / 2; j++) {
        int a = hex_digit(p->data[x.start + 2*j]), b = hex_digit(p->data[x.start + 2*j + 1]);
        if (a < 0 || b < 0) return 0;
        out[j] = (uint8_t)((a << 4) | b);
    }
    *size = n / 2;
    return 1;
}

int tornado_keystore_parse(const uint8_t *json, size_t size,
    tornado_keystore *out, tornado_key_status *status) {
    *status = TORNADO_KEY_KEYSTORE_FORMAT;
    memset(out, 0, sizeof(*out));
    if (size == 0 || size > TORNADO_MAX_KEYSTORE_FILE || !utf8(json, size)) return 0;
    json_parser parser = { .data = json, .size = size };
    size_t root;
    if (!value(&parser, 0, &root)) return 0;
    whitespace(&parser);
    if (root != 0 || parser.position != size || parser.tokens[0].kind != J_OBJECT) return 0;
    uint64_t version;
    if (!integer(&parser, field(&parser, 0, "version"), &version) || version != 3) {
        *status = TORNADO_KEY_KEYSTORE_UNSUPPORTED; return 0;
    }
    int crypto = field(&parser, 0, "crypto"), upper = field(&parser, 0, "Crypto");
    if ((crypto >= 0) == (upper >= 0)) return 0;
    if (crypto < 0) crypto = upper;
    if (!equals(&parser, field(&parser, crypto, "cipher"), "aes-128-ctr")) {
        *status = TORNADO_KEY_KEYSTORE_UNSUPPORTED; return 0;
    }
    size_t length;
    int params = field(&parser, crypto, "cipherparams");
    if (!hex_bytes(&parser, field(&parser, params, "iv"), out->iv, 16, 16, &length) ||
        !hex_bytes(&parser, field(&parser, crypto, "ciphertext"), out->ciphertext, 1, 32, &out->ciphertext_size) ||
        !hex_bytes(&parser, field(&parser, crypto, "mac"), out->mac, 32, 32, &length)) return 0;
    params = field(&parser, crypto, "kdfparams");
    uint64_t dklen;
    if (!integer(&parser, field(&parser, params, "dklen"), &dklen)) return 0;
    if (dklen < 32 || dklen > 1024) { *status = TORNADO_KEY_KEYSTORE_BUDGET; return 0; }
    out->dklen = (size_t)dklen;
    if (!hex_bytes(&parser, field(&parser, params, "salt"), out->salt, 1, sizeof(out->salt), &out->salt_size)) return 0;
    int kdf = field(&parser, crypto, "kdf");
    if (equals(&parser, kdf, "scrypt")) {
        out->scrypt = 1;
        if (!integer(&parser, field(&parser, params, "n"), &out->n) ||
            !integer(&parser, field(&parser, params, "r"), &out->r) ||
            !integer(&parser, field(&parser, params, "p"), &out->p)) return 0;
        /* Independent memory and work caps. Never lower requested parameters. */
        if (out->n < 2 || (out->n & (out->n - 1)) || out->n > (1u << 20) ||
            out->r == 0 || out->r > 1024 || out->p == 0 || out->p > 1024 ||
            128u * out->r * (out->n + out->p + 2u) > (512u * 1024u * 1024u) ||
            out->n * out->r * out->p > (1u << 25)) {
            *status = TORNADO_KEY_KEYSTORE_BUDGET; return 0;
        }
    } else if (equals(&parser, kdf, "pbkdf2")) {
        if (!equals(&parser, field(&parser, params, "prf"), "hmac-sha256")) {
            *status = TORNADO_KEY_KEYSTORE_UNSUPPORTED; return 0;
        }
        if (!integer(&parser, field(&parser, params, "c"), &out->iterations)) return 0;
        if (out->iterations == 0 || out->iterations > 10000000) {
            *status = TORNADO_KEY_KEYSTORE_BUDGET; return 0;
        }
    } else { *status = TORNADO_KEY_KEYSTORE_UNSUPPORTED; return 0; }
    int address = field(&parser, 0, "address");
    if (address >= 0) {
        if (parser.tokens[address].kind != J_STRING) return 0;
        token *a = &parser.tokens[address];
        if (a->end - a->start == 42 && json[a->start] == '0' && json[a->start + 1] == 'x') a->start += 2;
        if (!hex_bytes(&parser, address, out->address, 20, 20, &length)) return 0;
        out->has_address = 1;
    }
    *status = TORNADO_KEY_OK;
    return 1;
}

int tornado_keystore_keccak(const uint8_t *bytes, size_t size, uint8_t hash[32]) {
    EVP_MD *md = EVP_MD_fetch(NULL, "KECCAK-256", NULL);
    if (md == NULL) return 0;
    unsigned int length = 0;
    int ok = EVP_Digest(bytes, size, hash, &length, md, NULL) == 1 && length == 32;
    EVP_MD_free(md);
    return ok;
}
int tornado_keystore_fingerprint(const uint8_t *bytes, size_t size, uint8_t hash[32]) {
    unsigned int length = 0;
    return EVP_Digest(bytes, size, hash, &length, EVP_sha256(), NULL) == 1 && length == 32;
}

int tornado_keystore_decrypt(const tornado_keystore *store,
    const uint8_t *password, size_t password_size, uint8_t key32[32],
    uint8_t work[TORNADO_KEYSTORE_WORK_BYTES], tornado_key_status *status) {
    uint8_t *derived = work, *body = work + 1024, *mac = work + 1072;
    EVP_CIPHER_CTX *ctx = NULL;
    int ok = 0;
    memset(work, 0, TORNADO_KEYSTORE_WORK_BYTES);
    memset(key32, 0, 32);
    if (store->dklen < 32 || store->dklen > 1024 || store->salt_size == 0 ||
        store->salt_size > sizeof(store->salt) || store->ciphertext_size == 0 ||
        store->ciphertext_size > sizeof(store->ciphertext)) {
        *status = TORNADO_KEY_KEYSTORE_FORMAT; goto done;
    }
    if (!tornado_password_valid(password, password_size)) {
        *status = TORNADO_KEY_PASSWORD_FORMAT; goto done;
    }
    *status = TORNADO_KEY_KEYSTORE_CRYPTO;
    if (store->scrypt) {
        /* These bounds also protect downcasts and the backend allocation. */
        if (store->n < 2 || (store->n & (store->n - 1)) || store->n > (1u << 20) ||
            store->r == 0 || store->r > 1024 || store->p == 0 || store->p > 1024 ||
            128u * store->r * (store->n + store->p + 2u) > (512u * 1024u * 1024u) ||
            store->n * store->r * store->p > (1u << 25)) {
            *status = TORNADO_KEY_KEYSTORE_BUDGET; goto done;
        }
        if (sodium_init() < 0 || crypto_pwhash_scryptsalsa208sha256_ll(password,
                password_size, store->salt, store->salt_size, store->n,
                (uint32_t)store->r, (uint32_t)store->p, derived, store->dklen) != 0) goto done;
    } else if (store->iterations == 0 || store->iterations > 10000000) {
        *status = TORNADO_KEY_KEYSTORE_BUDGET; goto done;
    } else if (PKCS5_PBKDF2_HMAC((const char *)password, (int)password_size,
            store->salt, (int)store->salt_size, (int)store->iterations,
            EVP_sha256(), (int)store->dklen, derived) != 1) goto done;
    memcpy(body, derived + 16, 16);
    memcpy(body + 16, store->ciphertext, store->ciphertext_size);
    if (!tornado_keystore_keccak(body, 16 + store->ciphertext_size, mac)) goto done;
    if (CRYPTO_memcmp(mac, store->mac, 32) != 0) {
        *status = TORNADO_KEY_KEYSTORE_PASSWORD; goto done;
    }
    ctx = EVP_CIPHER_CTX_new();
    if (ctx == NULL || EVP_DecryptInit_ex(ctx, EVP_aes_128_ctr(), NULL, derived, store->iv) != 1) goto done;
    int produced = 0, final = 0;
    /* Historical geth v3 files can omit leading zero bytes of the scalar. */
    if (EVP_DecryptUpdate(ctx, key32 + 32 - store->ciphertext_size, &produced,
            store->ciphertext, (int)store->ciphertext_size) != 1 || produced != (int)store->ciphertext_size ||
        EVP_DecryptFinal_ex(ctx, mac, &final) != 1 || final != 0) goto done;
    ok = 1;
    *status = TORNADO_KEY_OK;
done:
    EVP_CIPHER_CTX_free(ctx);
    wipe(work, TORNADO_KEYSTORE_WORK_BYTES);
    if (!ok) wipe(key32, 32);
    return ok;
}
