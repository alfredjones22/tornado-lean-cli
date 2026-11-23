import { spawn } from 'node:child_process'
import { createServer } from 'node:http'
import { resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const requireCheck = (condition, message) => { if (!condition) throw new Error(message) }
const requests = []
let proxyRequests = 0
const handle = (request, response) => {
  const data = []
  request.on('data', chunk => data.push(chunk))
  request.on('end', () => {
    requests.push({ path: request.url, method: request.method,
      headers: request.headers, body: Buffer.concat(data).toString('utf8') })
    if (request.url === '/rpc?mode=loopback') response.end('{"jsonrpc":"2.0","id":1,"result":"0x1"}')
    else if (request.url === '/get') response.end('loopback get')
    else if (request.url === '/redirect') {
      response.statusCode = 302
      response.setHeader('Location', '/followed')
      response.end('redirect')
    } else if (request.url === '/bad-status') {
      response.statusCode = 500
      response.end('failed')
    } else if (request.url === '/oversize-response') response.end('x'.repeat(1048577))
    else if (request.url === '/oversize') response.end('12345')
    else if (request.url === '/empty') response.end()
    else {
      response.statusCode = 404
      response.end('unexpected')
    }
  })
}
const ipv4 = createServer(handle)
const ipv6 = createServer(handle)
const proxy = createServer((_request, response) => {
  proxyRequests++
  response.statusCode = 502
  response.end('ambient proxy must never be used')
})
const listen = (server, host) => new Promise((done, reject) => {
  server.once('error', reject)
  server.listen(0, host, () => {
    server.removeListener('error', reject)
    done()
  })
})
const close = server => new Promise(done => server.close(done))

try {
  await listen(ipv4, '127.0.0.1')
  await listen(ipv6, '::1')
  await listen(proxy, '127.0.0.1')
  const proxyUrl = `http://127.0.0.1:${proxy.address().port}`
  const env = { ...process.env, HTTP_PROXY: proxyUrl, HTTPS_PROXY: proxyUrl,
    ALL_PROXY: proxyUrl, http_proxy: proxyUrl, https_proxy: proxyUrl, all_proxy: proxyUrl,
    NO_PROXY: '', no_proxy: '' }
  const result = await new Promise((done, reject) => {
    const child = spawn(resolve(root, '.lake/build/bin/https_transport_test'), [
      'loopback', `http://127.0.0.1:${ipv4.address().port}`,
      `http://localhost:${ipv4.address().port}`, `http://[::1]:${ipv6.address().port}`,
    ], { cwd: root, env, timeout: 30000 })
    let stdout = '', stderr = ''
    child.stdout.on('data', chunk => { stdout += chunk })
    child.stderr.on('data', chunk => { stderr += chunk })
    child.on('error', reject)
    child.on('close', status => done({ status, stdout, stderr }))
  })
  requireCheck(result.status === 0, `Loopback HTTP test failed: ${result.stdout}${result.stderr}`)
  requireCheck(proxyRequests === 0, 'Loopback HTTP used an ambient proxy')
  const expected = ['/rpc?mode=loopback', '/get', '/redirect', '/redirect',
    '/bad-status', '/oversize-response', '/oversize', '/empty']
  requireCheck(JSON.stringify(requests.map(row => row.path)) === JSON.stringify([...expected, ...expected, ...expected]),
    `Unexpected loopback requests or followed redirect: ${JSON.stringify(requests.map(row => row.path))}`)
  requireCheck(requests.every(row => !row.headers.authorization && !row.headers.cookie),
    'Loopback HTTP sent authorization or cookies')
  requireCheck(requests.filter(row => row.path === '/rpc?mode=loopback').every(row =>
    row.method === 'POST' && row.body === '{}' && row.headers['content-type'] === 'application/json'),
    'Loopback POST body or headers changed')
  requireCheck(requests.filter(row => row.path === '/get').every(row =>
    row.method === 'GET' && row.headers['cache-control']?.includes('no-store')),
    'Loopback GET or no-cache semantics changed')
  process.stdout.write(result.stdout)
} finally {
  await Promise.all([close(ipv4), close(ipv6), close(proxy)])
}
