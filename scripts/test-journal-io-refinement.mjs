import { spawn, spawnSync } from 'node:child_process'
import { chmodSync, mkdtempSync, readdirSync, rmSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

// Disposable public-hash fixture. This probes the same compiled Lean/C journal
// path as the CLI would use; it does not sign, send, or contact an endpoint.
const root = fileURLToPath(new URL('../', import.meta.url))
const binary = resolve(root, '.lake/build/bin/journal_refinement_test')
const directory = mkdtempSync(join(root, '.journal-refinement-test-'))
chmodSync(directory, 0o700)
const preparedId = '1'.repeat(32)
const crashId = '2'.repeat(32)

function requireCheck(condition, reason) {
  if (!condition) throw new Error(reason)
}

function run(action, id) {
  const result = spawnSync(binary, [action, directory, id], {
    encoding: 'utf8', timeout: 30000, maxBuffer: 1024 * 1024,
  })
  if (result.error || result.signal) {
    throw new Error(`${action} process failed unexpectedly: ${result.error ?? result.signal}`)
  }
  return result
}

function concurrentArm(id) {
  return new Promise((resolvePromise, reject) => {
    const child = spawn(binary, ['arm', directory, id], {
      stdio: ['ignore', 'pipe', 'pipe'],
    })
    let stdout = '', stderr = ''
    child.stdout.setEncoding('utf8').on('data', chunk => { stdout += chunk })
    child.stderr.setEncoding('utf8').on('data', chunk => { stderr += chunk })
    child.on('error', reject)
    child.on('close', (status, signal) => resolvePromise({ status, signal, stdout, stderr }))
  })
}

try {
  const prep = run('prepare', preparedId)
  requireCheck(prep.status === 0 && prep.stdout.trim() === 'prepared',
    `Failed to prepare native journal: ${prep.stderr}`)

  let writeFailureTested = false
  // POSIX mode denial cannot be induced when the test runner itself is root.
  if (process.getuid?.() !== 0) {
    chmodSync(directory, 0o500)
    try {
      const rejected = run('arm', preparedId)
      requireCheck(rejected.status !== 0,
        'Arming unexpectedly succeeded in a nonwritable journal directory')
    } finally {
      chmodSync(directory, 0o700)
    }
    const replay = run('replay', preparedId)
    requireCheck(replay.status === 0 && replay.stdout.trim() === 'reserved:0',
      'A failed exposure-file write advanced the recoverable send state')
    requireCheck(readdirSync(directory).filter(name =>
      name.startsWith(`${preparedId}.`)).length === 3,
    'A failed exposure-file write left an advanced record')
    writeFailureTested = true
  }

  const race = await Promise.all([concurrentArm(preparedId), concurrentArm(preparedId)])
  requireCheck(race.filter(row => row.status === 0 && !row.signal &&
    row.stdout.trim() === 'armed').length === 1,
  `Two processes did not yield exactly one armed journal: ${JSON.stringify(race)}`)
  requireCheck(race.filter(row => row.status !== 0 || row.signal).length === 1,
    `Competing arm was not rejected: ${JSON.stringify(race)}`)
  const armed = run('replay', preparedId)
  requireCheck(armed.status === 0 && armed.stdout.trim() === 'submitted:1',
    'Concurrent arm lost the single consumed send slot')
  requireCheck(run('arm', preparedId).status !== 0,
    'A submitted attempt was armed a second time')

  requireCheck(run('prepare', crashId).status === 0, 'Crash fixture preparation failed')
  requireCheck(run('expose', crashId).status === 0, 'Crash fixture exposure failed')
  const exposed = run('replay', crashId)
  requireCheck(exposed.status === 0 && exposed.stdout.trim() === 'exposed:0',
    'Exposure-only crash fixture did not replay as terminal exposure')
  requireCheck(run('arm', crashId).status !== 0,
    'An exposed attempt was armed after a simulated crash')

  process.stdout.write(writeFailureTested
    ? 'Journal IO refinement: failed write, concurrent arm, and crash replay gates passed\n'
    : 'Journal IO refinement: concurrent arm and crash replay gates passed (write failure skipped as root)\n')
} finally {
  chmodSync(directory, 0o700)
  rmSync(directory, { recursive: true, force: true })
}
