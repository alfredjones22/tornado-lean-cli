# HTTPS GET boundary for public Saga assets

`HttpTransport.getSagaIndex` and `getSagaChunk` call the reviewed
`tornado_https_get` C/libcurl binding. The native binding accepts HTTPS and
explicit loopback HTTP for local fixtures, and rejects remote plaintext,
URL credentials and fragments, zero or greater than 32 MiB response
bounds, TLS verification failures, redirects, non-200 statuses, oversized
headers, and bodies exceeding the supplied bound. It disables proxies,
HTTP authentication and netrc. It uses a 10-second connect timeout and a
60-second total timeout. Index reads are limited to 2 MiB and request
`Cache-Control: no-store`; chunks are limited to 32 MiB, and hot chunks also
request no-cache headers.

libcurl decodes HTTP `Content-Encoding: gzip` or `deflate` before the bounded
body callback. A `.jsonl.gz` asset without that HTTP header remains compressed.
The Saga parser accepts either bounded form, then validates its SHA-256 digest
and event data. Empty GET bodies are allowed by the transport but rejected by
an index parser if invalid. The C binding returns opaque bytes; it does not
trust or interpret a Saga index, chain snapshot, event or RPC response.

The unit test invokes the *same* C body and header callbacks on exact-limit,
over-limit and integer-overflow inputs, and tests URL rejection without
network access. The local TLS test verifies that the binding refuses an
untrusted certificate. On Linux with a supported `CURL_CA_BUNDLE`, it also
tests a trusted local fetch, transport gzip decoding, raw `.gz` preservation,
size rejection, no redirect, 404 rejection, and no-cache request headers.
macOS system libcurl/SecureTransport does not use that temporary CA bundle,
so the trusted local fetch is skipped there; the production binding keeps the
system trust store and has no test-only CA bypass. A one-off macOS smoke test
of `https_get_test manual https://example.com` returned 577 bytes from a
system-trusted HTTPS endpoint on 2026-11-22; it is not part of the offline
verification gate.

This is an OS/TLS trust boundary, not a Lean proof of libcurl or server truth.
The GET functions serve bounded native history and withdrawal-session fetches.
A caller must check the selected chain and pool, keep the index
and all chunks within an aggregate resource budget, validate all bytes before
advertising coverage, and fall back safely after any error.
