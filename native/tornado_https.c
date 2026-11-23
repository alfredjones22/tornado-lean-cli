/*
 * Trusted HTTPS and explicit loopback HTTP socket boundary. Requests and
 * responses are opaque bytes here;
 * JSON-RPC method, encoding, response ID, and result checks stay in Lean.
 * No redirects, ambient proxies, cookies, HTTP auth, or insecure TLS fallback.
 */
#include <lean/lean.h>
#include <curl/curl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/socket.h>
#include <netinet/in.h>

#define TORNADO_HTTP_LIMIT (1024u * 1024u)
#define TORNADO_URL_LIMIT 2048u
#define TORNADO_HEADER_LIMIT (64u * 1024u)

struct response_buffer { uint8_t *data; size_t size; size_t limit; };
struct header_counter { size_t size; };
#ifndef TORNADO_HTTPS_UNIT_TEST
static pthread_once_t curl_once = PTHREAD_ONCE_INIT;
static CURLcode curl_init_result = CURLE_FAILED_INIT;
static void init_curl(void) { curl_init_result = curl_global_init(CURL_GLOBAL_DEFAULT); }
static lean_obj_res failure(const char *reason) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(reason)));
}
#endif

static size_t receive_body(char *chunk, size_t size, size_t count, void *user) {
    struct response_buffer *out = (struct response_buffer *)user;
    if (size != 0 && count > SIZE_MAX / size) return 0;
    size_t length = size * count;
    if (out->size > out->limit || length > out->limit - out->size) return 0;
    uint8_t *next = realloc(out->data, out->size + length + 1);
    if (next == NULL) return 0;
    memcpy(next + out->size, chunk, length);
    out->data = next;
    out->size += length;
    return length;
}

static size_t receive_header(char *chunk, size_t size, size_t count, void *user) {
    (void)chunk;
    struct header_counter *counter = (struct header_counter *)user;
    if (size != 0 && count > SIZE_MAX / size) return 0;
    size_t length = size * count;
    if (length > TORNADO_HEADER_LIMIT - counter->size) return 0;
    counter->size += length;
    return length;
}

enum request_protocol { URL_REJECTED = 0, URL_HTTPS = 1, URL_LOOPBACK_HTTP = 2 };

/* Check the original authority, before curl can normalize alternate numeric
 * IPv4 spellings, percent escapes or expanded IPv6 forms. Plain HTTP is an
 * explicit local-development exception, never an insecure HTTPS fallback. */
static int explicit_loopback_authority(const char *raw) {
    if (strncasecmp(raw, "http://", 7) != 0) return 0;
    if (strchr(raw, '#') != NULL) return 0;
    for (const unsigned char *p = (const unsigned char *)raw; *p; ++p)
        if (*p <= 0x20 || *p >= 0x7f) return 0;
    const char *authority = raw + 7;
    size_t length = strcspn(authority, "/?#");
    size_t host_length;
    if (length >= 5 && memcmp(authority, "[::1]", 5) == 0) host_length = 5;
    else {
        host_length = 0;
        while (host_length < length && authority[host_length] != ':') ++host_length;
        if (!((host_length == 9 && memcmp(authority, "127.0.0.1", 9) == 0) ||
              (host_length == 9 && strncasecmp(authority, "localhost", 9) == 0)))
            return 0;
    }
    if (host_length == length) return 1;
    if (authority[host_length] != ':') return 0;
    size_t port_length = length - host_length - 1;
    if (port_length == 0 || port_length > 5 || authority[host_length + 1] == '0') return 0;
    unsigned int port = 0;
    for (size_t i = host_length + 1; i < length; ++i) {
        if (authority[i] < '0' || authority[i] > '9') return 0;
        port = port * 10u + (unsigned int)(authority[i] - '0');
    }
    return port > 0 && port <= 65535u;
}

static int allowed_url(const char *raw) {
    CURLU *parsed = curl_url();
    char *scheme = NULL, *host = NULL, *user = NULL, *password = NULL, *fragment = NULL;
    if (parsed == NULL) return 0;
    int okay = strlen(raw) < TORNADO_URL_LIMIT &&
        curl_url_set(parsed, CURLUPART_URL, raw, 0) == CURLUE_OK &&
        curl_url_get(parsed, CURLUPART_SCHEME, &scheme, 0) == CURLUE_OK &&
        curl_url_get(parsed, CURLUPART_HOST, &host, 0) == CURLUE_OK &&
        scheme != NULL &&
        host != NULL && host[0] != '\0' &&
        curl_url_get(parsed, CURLUPART_USER, &user, 0) != CURLUE_OK &&
        curl_url_get(parsed, CURLUPART_PASSWORD, &password, 0) != CURLUE_OK &&
        curl_url_get(parsed, CURLUPART_FRAGMENT, &fragment, 0) != CURLUE_OK;
    int protocol = URL_REJECTED;
    if (okay && strcmp(scheme, "https") == 0) protocol = URL_HTTPS;
    else if (okay && strcasecmp(scheme, "http") == 0 &&
             explicit_loopback_authority(raw) &&
             (strcmp(host, "127.0.0.1") == 0 || strcasecmp(host, "localhost") == 0 ||
              strcmp(host, "[::1]") == 0)) protocol = URL_LOOPBACK_HTTP;
    curl_free(scheme); curl_free(host); curl_free(user);
    curl_free(password); curl_free(fragment); curl_url_cleanup(parsed);
    return protocol;
}

/* Even a changed localhost DNS/hosts entry must not carry a plaintext RPC
 * to a remote peer. Restrict the actual socket destination as well as URL
 * spelling. HTTPS sockets retain their existing behavior. */
static int loopback_destination(int family, const struct sockaddr *address,
                                size_t length) {
    if (family == AF_INET && length >= sizeof(struct sockaddr_in)) {
        const struct sockaddr_in *peer = (const struct sockaddr_in *)address;
        return ntohl(peer->sin_addr.s_addr) == 0x7f000001u;
    }
    if (family == AF_INET6 && length >= sizeof(struct sockaddr_in6)) {
        const struct sockaddr_in6 *peer = (const struct sockaddr_in6 *)address;
        static const uint8_t local[16] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 };
        return memcmp(&peer->sin6_addr, local, sizeof(local)) == 0;
    }
    return 0;
}

#ifndef TORNADO_HTTPS_UNIT_TEST
static curl_socket_t open_loopback_socket(void *user, curlsocktype purpose,
                                        struct curl_sockaddr *address) {
    (void)user;
    if (purpose != CURLSOCKTYPE_IPCXN ||
        !loopback_destination(address->family, &address->addr, address->addrlen))
        return CURL_SOCKET_BAD;
    return socket(address->family, address->socktype, address->protocol);
}

LEAN_EXPORT lean_obj_res tornado_https_post(
    b_lean_obj_arg url, b_lean_obj_arg body, lean_obj_arg world) {
    (void)world;
    size_t url_size = lean_string_size(url);
    size_t body_size = lean_sarray_size(body);
    const char *raw_url = lean_string_cstr(url);
    if (url_size < 9 || url_size > TORNADO_URL_LIMIT ||
        strlen(raw_url) != url_size - 1 || body_size > TORNADO_HTTP_LIMIT)
        return failure("HTTPS endpoint or request size is invalid");
    int protocol = allowed_url(raw_url);
    if (protocol == URL_REJECTED) return failure("HTTPS endpoint or request size is invalid");
    if (pthread_once(&curl_once, init_curl) != 0 || curl_init_result != CURLE_OK)
        return failure("HTTPS library initialization failed");

    CURL *curl = curl_easy_init();
    struct curl_slist *headers = NULL;
    struct response_buffer response = { NULL, 0, TORNADO_HTTP_LIMIT };
    struct header_counter header_count = { 0 };
    if (curl == NULL) return failure("HTTPS handle allocation failed");
    headers = curl_slist_append(headers, "Content-Type: application/json");
    if (headers == NULL) { curl_easy_cleanup(curl); return failure("HTTPS header allocation failed"); }
    struct curl_slist *next = curl_slist_append(headers, "Accept: application/json");
    if (next == NULL) {
        curl_slist_free_all(headers); curl_easy_cleanup(curl);
        return failure("HTTPS header allocation failed");
    }
    headers = next;
    next = curl_slist_append(headers, "Expect:");
    if (next == NULL) {
        curl_slist_free_all(headers); curl_easy_cleanup(curl);
        return failure("HTTPS header allocation failed");
    }
    headers = next;

    CURLcode configured = CURLE_OK;
#define SETOPT(option, value) do { if (configured == CURLE_OK) configured = curl_easy_setopt(curl, option, value); } while (0)
    SETOPT(CURLOPT_URL, raw_url);
    SETOPT(CURLOPT_HTTPHEADER, headers);
    SETOPT(CURLOPT_POST, 1L);
    SETOPT(CURLOPT_POSTFIELDS, lean_sarray_cptr((lean_object *)body));
    SETOPT(CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)body_size);
    SETOPT(CURLOPT_WRITEFUNCTION, receive_body);
    SETOPT(CURLOPT_WRITEDATA, &response);
    SETOPT(CURLOPT_HEADERFUNCTION, receive_header);
    SETOPT(CURLOPT_HEADERDATA, &header_count);
    SETOPT(CURLOPT_PROTOCOLS_STR, protocol == URL_LOOPBACK_HTTP ? "http" : "https");
    if (protocol == URL_LOOPBACK_HTTP) SETOPT(CURLOPT_OPENSOCKETFUNCTION, open_loopback_socket);
    SETOPT(CURLOPT_FOLLOWLOCATION, 0L);
    SETOPT(CURLOPT_MAXREDIRS, 0L);
    SETOPT(CURLOPT_PROXY, "");
    SETOPT(CURLOPT_NOPROXY, "*");
    SETOPT(CURLOPT_HTTPAUTH, CURLAUTH_NONE);
    SETOPT(CURLOPT_PROXYAUTH, CURLAUTH_NONE);
    SETOPT(CURLOPT_NETRC, CURL_NETRC_IGNORED);
    SETOPT(CURLOPT_SSL_VERIFYPEER, 1L);
    SETOPT(CURLOPT_SSL_VERIFYHOST, 2L);
    SETOPT(CURLOPT_SSLVERSION, CURL_SSLVERSION_TLSv1_2);
    SETOPT(CURLOPT_CONNECTTIMEOUT_MS, 10000L);
    SETOPT(CURLOPT_TIMEOUT_MS, 30000L);
    SETOPT(CURLOPT_NOSIGNAL, 1L);
    SETOPT(CURLOPT_USERAGENT, "tornado-lean-cli/0.1");
#undef SETOPT

    CURLcode result = configured == CURLE_OK ? curl_easy_perform(curl) : configured;
    long status = 0;
    if (result == CURLE_OK) result = curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &status);
    curl_slist_free_all(headers);
    curl_easy_cleanup(curl);
    if (result != CURLE_OK) {
        free(response.data);
        if (result == CURLE_COULDNT_RESOLVE_HOST || result == CURLE_COULDNT_CONNECT ||
            result == CURLE_OPERATION_TIMEDOUT || result == CURLE_SEND_ERROR ||
            result == CURLE_RECV_ERROR || result == CURLE_GOT_NOTHING)
            return failure("HTTPS transport unavailable");
        return failure("HTTPS request rejected or exceeded bounds");
    }
    if (status != 200 || response.size == 0) {
        free(response.data);
        if (status == 500 || status == 502 || status == 503 || status == 504)
            return failure("HTTPS transport unavailable");
        return failure("HTTPS request rejected or exceeded bounds");
    }
    lean_object *bytes = lean_alloc_sarray(1, response.size, response.size);
    memcpy(lean_sarray_cptr(bytes), response.data, response.size);
    free(response.data);
    return lean_io_result_mk_ok(bytes);
}

/* The only GET operation is bounded at the native boundary as well as at its
 * Lean call sites. curl decodes HTTP Content-Encoding into this bounded write
 * callback. A .jsonl.gz asset without Content-Encoding remains compressed and
 * is checked by the Lean gzip/digest parser; an HTTP-encoded response is
 * decoded once by curl and then checked by the same parser. */
#define TORNADO_GET_LIMIT (32u * 1024u * 1024u)

LEAN_EXPORT lean_obj_res tornado_https_get(
    b_lean_obj_arg url, uint32_t max_bytes, uint8_t no_cache,
    lean_obj_arg world) {
    (void)world;
    size_t url_size = lean_string_size(url);
    const char *raw_url = lean_string_cstr(url);
    if (url_size < 9 || url_size > TORNADO_URL_LIMIT ||
        strlen(raw_url) != url_size - 1 || max_bytes == 0 ||
        max_bytes > TORNADO_GET_LIMIT)
        return failure("HTTPS GET endpoint or response bound is invalid");
    int protocol = allowed_url(raw_url);
    if (protocol == URL_REJECTED) return failure("HTTPS GET endpoint or response bound is invalid");
    if (pthread_once(&curl_once, init_curl) != 0 || curl_init_result != CURLE_OK)
        return failure("HTTPS library initialization failed");

    CURL *curl = curl_easy_init();
    struct curl_slist *headers = NULL;
    struct response_buffer response = { NULL, 0, (size_t)max_bytes };
    struct header_counter header_count = { 0 };
    if (curl == NULL) return failure("HTTPS handle allocation failed");
    headers = curl_slist_append(headers, "Accept: */*");
    if (headers == NULL) {
        curl_easy_cleanup(curl);
        return failure("HTTPS header allocation failed");
    }
    if (no_cache) {
        struct curl_slist *next = curl_slist_append(headers,
            "Cache-Control: no-store, no-cache, max-age=0");
        if (next == NULL) {
            curl_slist_free_all(headers); curl_easy_cleanup(curl);
            return failure("HTTPS header allocation failed");
        }
        headers = next;
        next = curl_slist_append(headers, "Pragma: no-cache");
        if (next == NULL) {
            curl_slist_free_all(headers); curl_easy_cleanup(curl);
            return failure("HTTPS header allocation failed");
        }
        headers = next;
    }

    CURLcode configured = CURLE_OK;
#define SETOPT(option, value) do { if (configured == CURLE_OK) configured = curl_easy_setopt(curl, option, value); } while (0)
    SETOPT(CURLOPT_URL, raw_url);
    SETOPT(CURLOPT_HTTPHEADER, headers);
    SETOPT(CURLOPT_HTTPGET, 1L);
    SETOPT(CURLOPT_WRITEFUNCTION, receive_body);
    SETOPT(CURLOPT_WRITEDATA, &response);
    SETOPT(CURLOPT_HEADERFUNCTION, receive_header);
    SETOPT(CURLOPT_HEADERDATA, &header_count);
    SETOPT(CURLOPT_PROTOCOLS_STR, protocol == URL_LOOPBACK_HTTP ? "http" : "https");
    if (protocol == URL_LOOPBACK_HTTP) SETOPT(CURLOPT_OPENSOCKETFUNCTION, open_loopback_socket);
    SETOPT(CURLOPT_FOLLOWLOCATION, 0L);
    SETOPT(CURLOPT_MAXREDIRS, 0L);
    SETOPT(CURLOPT_PROXY, "");
    SETOPT(CURLOPT_NOPROXY, "*");
    SETOPT(CURLOPT_HTTPAUTH, CURLAUTH_NONE);
    SETOPT(CURLOPT_PROXYAUTH, CURLAUTH_NONE);
    SETOPT(CURLOPT_NETRC, CURL_NETRC_IGNORED);
    SETOPT(CURLOPT_SSL_VERIFYPEER, 1L);
    SETOPT(CURLOPT_SSL_VERIFYHOST, 2L);
    SETOPT(CURLOPT_SSLVERSION, CURL_SSLVERSION_TLSv1_2);
    SETOPT(CURLOPT_ACCEPT_ENCODING, "gzip,deflate");
    SETOPT(CURLOPT_HTTP_CONTENT_DECODING, 1L);
    SETOPT(CURLOPT_MAXFILESIZE_LARGE, (curl_off_t)max_bytes);
    SETOPT(CURLOPT_CONNECTTIMEOUT_MS, 10000L);
    SETOPT(CURLOPT_TIMEOUT_MS, 60000L);
    SETOPT(CURLOPT_NOSIGNAL, 1L);
    SETOPT(CURLOPT_USERAGENT, "tornado-lean-cli/0.1");
#undef SETOPT

    CURLcode result = configured == CURLE_OK ? curl_easy_perform(curl) : configured;
    long status = 0;
    if (result == CURLE_OK)
        result = curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &status);
    curl_slist_free_all(headers);
    curl_easy_cleanup(curl);
    if (result != CURLE_OK || status != 200) {
        free(response.data);
        return failure("HTTPS GET failed, returned non-200 status, or exceeded response bound");
    }
    lean_object *bytes = lean_alloc_sarray(1, response.size, response.size);
    if (response.size != 0) memcpy(lean_sarray_cptr(bytes), response.data, response.size);
    free(response.data);
    return lean_io_result_mk_ok(bytes);
}
#endif
