import { spawn, spawnSync } from 'node:child_process'
import { createServer } from 'node:https'
import { mkdtempSync, readFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { gzipSync } from 'node:zlib'

const root = fileURLToPath(new URL('../', import.meta.url))
const testRoot = mkdtempSync(join(tmpdir(), 'tornado-https-get-test-'))
const requireCheck = (condition, message) => { if (!condition) throw new Error(message) }

async function run(binary, args, env) {
  return await new Promise((done, reject) => {
    const child = spawn(binary, args, { cwd: root, env, timeout: 30000 })
    let stdout = ''
    let stderr = ''
    child.stdout.on('data', chunk => { stdout += chunk })
    child.stderr.on('data', chunk => { stderr += chunk })
    child.on('error', reject)
    child.on('close', status => done({ status, stdout, stderr }))
  })
}

try {
  const key = join(testRoot, 'key.pem')
  const cert = join(testRoot, 'cert.pem')
  const generated = spawnSync('openssl', ['req', '-x509', '-newkey', 'rsa:2048',
    '-nodes', '-keyout', key, '-out', cert, '-days', '1',
    '-subj', '/CN=127.0.0.1', '-addext', 'subjectAltName=IP:127.0.0.1'],
  { encoding: 'utf8', timeout: 10000 })
  if (generated.error || generated.status !== 0) {
    throw new Error(`Local GET certificate failed: ${generated.stderr}`)
  }

  const requests = []
  let rejectedHandshakes = 0
  const server = createServer({ key: readFileSync(key), cert: readFileSync(cert) },
    (request, response) => {
      requests.push({ path: request.url, method: request.method,
        headers: request.headers })
      if (request.url === '/index') {
        response.setHeader('Content-Type', 'application/json')
        response.end('{"version":2}')
      } else if (request.url === '/chunk') {
        response.setHeader('Content-Encoding', 'gzip')
        response.end(gzipSync('{"blockNumber":"0x1"}\n'))
      } else if (request.url === '/hot') {
        response.setHeader('Content-Type', 'application/gzip')
        response.end(gzipSync('{"blockNumber":"0x2"}\n'))
      } else if (request.url === '/oversize') {
        response.end('12345')
      } else if (request.url === '/redirect') {
        response.statusCode = 302
        response.setHeader('Location', '/index')
        response.end('redirect')
      } else if (request.url === '/empty') {
        response.end()
      } else {
        response.statusCode = 404
        response.end('missing')
      }
    })
  server.on('tlsClientError', () => { rejectedHandshakes++ })
  await new Promise(done => server.listen(0, '127.0.0.1', done))
  try {
    const base = `https://127.0.0.1:${server.address().port}`
    const binary = resolve(root, '.lake/build/bin/https_get_test')
    const unsafeEnv = { ...process.env }
    delete unsafeEnv.CURL_CA_BUNDLE
    delete unsafeEnv.SSL_CERT_FILE
    const unsafe = await run(binary, ['unsafe', base], unsafeEnv)
    requireCheck(unsafe.status === 0 && requests.length === 0 &&
      rejectedHandshakes > 0,
    `Unsafe GET checks failed: ${unsafe.stdout}${unsafe.stderr}`)

    if (process.platform === 'darwin') {
      // System libcurl/SecureTransport does not use CURL_CA_BUNDLE or
      // SSL_CERT_FILE as a temporary trust store. No test-specific trust
      // override is added to the production binding.
      process.stdout.write(unsafe.stdout +
        'HTTPS GET: trusted local fetch skipped on macOS system trust\n')
    } else {
      const positiveEnv = { ...process.env, CURL_CA_BUNDLE: cert,
        SSL_CERT_FILE: cert, HTTPS_PROXY: 'http://127.0.0.1:9' }
      const positive = await run(binary, ['positive', base], positiveEnv)
      requireCheck(positive.status === 0,
        `Trusted local GET checks failed after ${requests.length} requests and ${rejectedHandshakes} rejected handshakes: ${positive.stdout}${positive.stderr}`)
      requireCheck(requests.length === 7 && requests.every(row => row.method === 'GET'),
        `GET request count or method changed: ${JSON.stringify(requests)}`)
      const paths = requests.map(row => row.path)
      requireCheck(JSON.stringify(paths) === JSON.stringify([
        '/index', '/chunk', '/hot', '/oversize', '/redirect', '/missing', '/empty']),
      `GET path or redirect behavior changed: ${JSON.stringify(paths)}`)
      const index = requests[0].headers
      const chunk = requests[1].headers
      const hot = requests[2].headers
      requireCheck(index['cache-control']?.includes('no-store') &&
        hot['cache-control']?.includes('no-store') && hot.pragma === 'no-cache' &&
        !chunk['cache-control'] && chunk['accept-encoding']?.includes('gzip') &&
        chunk['accept-encoding']?.includes('deflate') &&
        requests.every(row => !row.headers.authorization && !row.headers.cookie),
      'GET headers, cache control, or forbidden credentials changed')
      process.stdout.write(unsafe.stdout + positive.stdout)
    }
  } finally {
    await new Promise(done => server.close(done))
  }
} finally {
  rmSync(testRoot, { recursive: true, force: true })
}
