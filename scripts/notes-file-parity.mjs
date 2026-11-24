import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { chmodSync, existsSync, mkdtempSync, readFileSync, rmSync,
  symlinkSync, writeFileSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { assertOracleIdentity } from './oracle-identity.mjs'

const root = fileURLToPath(new URL('../', import.meta.url))
const cli = resolve(process.env.TORNADO_TS_CLI ?? resolve(root, '../tornado-cli-new-era'))
assertOracleIdentity(cli)
const lean = resolve(root, '.lake/build/bin/tornado')
const ts = resolve(cli, 'bin/tornado.mjs')
const expectedDistHash = 'cb039416616458ab261036e08e3c4d83991a1b6d7ab4259328894292c035f809'
const digest = bytes => createHash('sha256').update(bytes).digest('hex')
const run = (executable, args, cwd) => {
  const process = spawnSync(executable, args, { cwd, encoding: 'utf8', timeout: 30000,
    maxBuffer: 1024 * 1024 })
  if (process.error || process.signal) throw process.error ?? new Error(`${executable} terminated`)
  return { status: process.status, stdout: process.stdout, stderr: process.stderr }
}
if (!existsSync(lean) || digest(readFileSync(resolve(cli, 'dist/index.js'))) !== expectedDistHash) {
  throw new Error('Build the Lean executable and keep the pinned TypeScript oracle dist unchanged')
}
const vectors = JSON.parse(readFileSync(resolve(root, 'fixtures/seeded-note-vectors.json'), 'utf8'))
const notes = vectors.groups[0].notes.map(row => row.raw)
const testRoot = mkdtempSync(join(root, '.notes-parity-'))
let passed = 0
try {
  chmodSync(testRoot, 0o700)
  const valid = join(testRoot, 'valid')
  const duplicate = join(testRoot, 'duplicate')
  const publicFile = join(testRoot, 'public')
  const symlink = join(testRoot, 'symlink')
  writeFileSync(valid, notes.join('\n') + '\n', { mode: 0o600 })
  writeFileSync(duplicate, [notes[0], notes[0]].join('\n') + '\n', { mode: 0o600 })
  writeFileSync(publicFile, notes[0] + '\n', { mode: 0o644 })
  chmodSync(publicFile, 0o644)
  symlinkSync(valid, symlink)
  const cases = [
    ['inspect one', 'inspect', valid, '1', true, 4],
    ['invoice four', 'invoice', valid, '1', true, 4],
    ['wrong chain', 'inspect', valid, '11155111', false],
    ['duplicate', 'inspect', duplicate, '1', false],
    ['public file', 'invoice', publicFile, '1', false],
    ['symlink', 'inspect', symlink, '1', false],
  ]
  for (const [name, command, path, chain, success, lines] of cases) {
    const args = ['notes', command, '--file', path, '--chain', chain]
    const oracle = run(process.execPath, [ts, ...args], cli)
    const native = run(lean, args, root)
    if (success) {
      if (oracle.status !== 0 || native.status !== 0 ||
          oracle.stdout !== native.stdout || oracle.stderr !== native.stderr ||
          native.stdout.trimEnd().split('\n').length !== lines) {
        throw new Error(`Read-only note parity mismatch: ${name}`)
      }
    } else if (oracle.status === 0 || native.status === 0 ||
        oracle.stdout !== '' || native.stdout !== '') {
      throw new Error(`Unsafe note-file case was accepted: ${name}`)
    }
    passed++
  }
  console.log(`Native note inspect/invoice: ${passed} pinned read-only parity and rejection checks passed`)
} finally {
  rmSync(testRoot, { recursive: true, force: true })
}
