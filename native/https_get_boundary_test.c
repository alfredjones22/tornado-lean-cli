#define TORNADO_HTTPS_UNIT_TEST 1
#include "tornado_https.c"
#include <assert.h>
#include <stdio.h>

int main(void) {
    struct response_buffer body = { NULL, 0, 4 };
    assert(receive_body("1234", 1, 4, &body) == 4);
    assert(body.size == 4 && memcmp(body.data, "1234", 4) == 0);
    assert(receive_body("5", 1, 1, &body) == 0 && body.size == 4);
    assert(receive_body("x", SIZE_MAX, 2, &body) == 0 && body.size == 4);
    free(body.data);

    struct header_counter headers = { 0 };
    assert(receive_header("", 1, TORNADO_HEADER_LIMIT, &headers) ==
        TORNADO_HEADER_LIMIT);
    assert(receive_header("", 1, 1, &headers) == 0);
    assert(allowed_url("https://example.com/path"));
    assert(!allowed_url("http://example.com/path"));
    assert(!allowed_url("https://user:pass@example.com/path"));
    assert(!allowed_url("https://example.com/path#fragment"));
    assert(allowed_url("http://127.0.0.1:8545/rpc?mode=dev") == URL_LOOPBACK_HTTP);
    assert(allowed_url("http://localhost:8545/") == URL_LOOPBACK_HTTP);
    assert(allowed_url("http://LOCALHOST:8545/") == URL_LOOPBACK_HTTP);
    assert(allowed_url("HTTP://LOCALHOST:8545/") == URL_LOOPBACK_HTTP);
    assert(allowed_url("http://[::1]:8545/") == URL_LOOPBACK_HTTP);
    assert(allowed_url("http://localhost/") == URL_LOOPBACK_HTTP);
    const char *rejected[] = {
        "http://127.0.0.2/", "http://127.1/", "http://2130706433/",
        "http://0177.0.0.1/", "http://0x7f000001/", "http://%6cocalhost/",
        "http://localhost./", "http://localhost.example.org/",
        "http://[::ffff:127.0.0.1]/", "http://[0:0:0:0:0:0:0:1]/",
        "http://[::1%25lo0]/", "http://user:pass@localhost/", "http://@localhost/",
        "http://localhost/#fragment", "http://localhost/#", "http://localhost:0/",
        "http://localhost:08545/", "http://localhost:+8545/", "http://localhost:65536/",
        "http://localhost:/", "http://localhost\\@example.org/", "http://localhost /",
        "file:///etc/passwd", "ftp://localhost/"
    };
    for (size_t i = 0; i < sizeof(rejected) / sizeof(rejected[0]); ++i)
        assert(!allowed_url(rejected[i]));
    struct sockaddr_in ipv4;
    memset(&ipv4, 0, sizeof(ipv4));
    ipv4.sin_family = AF_INET;
    ipv4.sin_addr.s_addr = htonl(0x7f000001u);
    assert(loopback_destination(AF_INET, (const struct sockaddr *)&ipv4, sizeof(ipv4)));
    ipv4.sin_addr.s_addr = htonl(0x7f000002u);
    assert(!loopback_destination(AF_INET, (const struct sockaddr *)&ipv4, sizeof(ipv4)));
    ipv4.sin_addr.s_addr = htonl(0x0a000001u);
    assert(!loopback_destination(AF_INET, (const struct sockaddr *)&ipv4, sizeof(ipv4)));
    struct sockaddr_in6 ipv6;
    memset(&ipv6, 0, sizeof(ipv6));
    ipv6.sin6_family = AF_INET6;
    ((uint8_t *)&ipv6.sin6_addr)[15] = 1;
    assert(loopback_destination(AF_INET6, (const struct sockaddr *)&ipv6, sizeof(ipv6)));
    assert(!loopback_destination(AF_INET6, (const struct sockaddr *)&ipv6, 1));
    ((uint8_t *)&ipv6.sin6_addr)[0] = 0x20;
    assert(!loopback_destination(AF_INET6, (const struct sockaddr *)&ipv6, sizeof(ipv6)));
    puts("HTTPS GET C boundary: callback, header, and URL guards passed");
    return 0;
}
