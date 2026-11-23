import { spawn, spawnSync } from 'node:child_process'
import { createServer } from 'node:https'
import { mkdtempSync, readFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const testRoot = mkdtempSync(join(tmpdir(), 'tornado-https-test-'))
try {
  const key = join(testRoot, 'key.pem')
  const cert = join(testRoot, 'cert.pem')
  const generated = spawnSync('openssl', ['req', '-x509', '-newkey', 'rsa:2048',
    '-nodes', '-keyout', key, '-out', cert, '-days', '1', '-subj', '/CN=localhost'],
    { encoding: 'utf8', timeout: 10000 })
  if (generated.error || generated.status !== 0) {
    throw new Error(`Local test certificate failed: ${generated.stderr}`)
  }
  let servedRequests = 0
  let rejectedHandshakes = 0
  const server = createServer({ key: readFileSync(key), cert: readFileSync(cert) },
    (_request, response) => {
      servedRequests++
      response.end('{"jsonrpc":"2.0","id":1,"result":"0x1"}')
    })
  server.on('tlsClientError', () => { rejectedHandshakes++ })
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve))
  try {
    const { port } = server.address()
    const binary = resolve(root, '.lake/build/bin/https_transport_test')
    const result = await new Promise((resolve, reject) => {
      const child = spawn(binary, [`https://127.0.0.1:${port}`], { timeout: 30000 })
      let stdout = ''
      let stderr = ''
      child.stdout.on('data', chunk => { stdout += chunk })
      child.stderr.on('data', chunk => { stderr += chunk })
      child.on('error', reject)
      child.on('close', status => resolve({ status, stdout, stderr }))
    })
    if (result.status !== 0 || servedRequests !== 0 || rejectedHandshakes === 0) {
      throw new Error(`HTTPS certificate rejection test failed:\n${result.stdout}\n${result.stderr}`)
    }
    process.stdout.write(result.stdout)
  } finally {
    server.close()
  }
} finally {
  rmSync(testRoot, { recursive: true, force: true })
}
