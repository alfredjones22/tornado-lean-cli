import { spawn, spawnSync } from 'node:child_process'
import { chmodSync, mkdirSync, mkdtempSync, rmSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const binary = resolve(root, '.lake/build/bin/note_claims_test')

function makeRoot() {
  const directory = mkdtempSync(join(root, '.note-claims-test-'))
  chmodSync(directory, 0o700)
  for (const subdir of ['claims', 'attempts']) {
    mkdirSync(join(directory, subdir), { mode: 0o700 })
    chmodSync(join(directory, subdir), 0o700)
  }
  return directory
}

function run(args) {
  const result = spawnSync(binary, args, { encoding: 'utf8', timeout: 30000 })
  if (result.error || result.signal) {
    throw new Error(`Note-claim test process failed: ${result.error ?? result.signal}`)
  }
  return result
}

function runConcurrent(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(binary, args, { stdio: ['ignore', 'pipe', 'pipe'] })
    let stdout = ''
    let stderr = ''
    child.stdout.setEncoding('utf8').on('data', chunk => { stdout += chunk })
    child.stderr.setEncoding('utf8').on('data', chunk => { stderr += chunk })
    child.on('error', reject)
    child.on('close', (status, signal) => resolve({ status, signal, stdout, stderr }))
  })
}

const directory = makeRoot()
const raceDirectory = makeRoot()
const unsafeDirectory = makeRoot()
try {
  const privacyNote = '0x' + 'f'.repeat(64)
  const privacyId = 'a'.repeat(32)
  chmodSync(join(unsafeDirectory, 'claims'), 0o755)
  if (run(['claim-only', unsafeDirectory, privacyId, privacyNote]).status === 0) {
    throw new Error('World-listable claims directory was accepted')
  }
  chmodSync(join(unsafeDirectory, 'claims'), 0o700)
  chmodSync(join(unsafeDirectory, 'attempts'), 0o755)
  if (run(['claim-only', unsafeDirectory, privacyId, privacyNote]).status === 0) {
    throw new Error('World-listable attempts directory was accepted')
  }
  chmodSync(join(unsafeDirectory, 'attempts'), 0o700)
  if (run(['claim-only', unsafeDirectory, privacyId, privacyNote]).status !== 0) {
    throw new Error('Owner-only claim directories were rejected')
  }
  chmodSync(join(unsafeDirectory, 'claims'), 0o755)
  if (run(['read-claim', unsafeDirectory, privacyNote]).status === 0) {
    throw new Error('A claim was readable after its directory became world-listable')
  }
  chmodSync(join(unsafeDirectory, 'claims'), 0o700)
  if (run(['read-claim', unsafeDirectory, privacyNote]).status !== 0) {
    throw new Error('A claim was not readable after owner-only permissions were restored')
  }

  const result = run([directory])
  if (result.status !== 0 || result.stdout.trim() !==
      'Note claims: exclusive direct/batch reservations, replay, unknown, conflict and orphan checks passed') {
    throw new Error(`Note-claim replay test failed:\n${result.stdout}\n${result.stderr}`)
  }

  const note = '0x' + '8'.repeat(64)
  const ids = ['8'.repeat(32), '9'.repeat(32)]
  const outcomes = await Promise.all(ids.map(id =>
    runConcurrent(['claim-only', raceDirectory, id, note])))
  if (outcomes.filter(outcome => outcome.status === 0 && !outcome.signal).length !== 1 ||
      outcomes.filter(outcome => outcome.status !== 0 || outcome.signal).length !== 1) {
    throw new Error(`Concurrent exclusive claims were not serialized: ${JSON.stringify(outcomes)}`)
  }
  const winner = ids[outcomes.findIndex(outcome => outcome.status === 0)]
  const loaded = run(['read-claim', raceDirectory, note])
  if (loaded.status !== 0 || loaded.stdout.trim() !== winner) {
    throw new Error('Winning concurrent claim was not durable and attributable')
  }
  process.stdout.write('Note claims: private directory, replay, conflicts, orphan safety, and concurrent exclusivity passed\n')
} finally {
  rmSync(directory, { recursive: true, force: true })
  rmSync(raceDirectory, { recursive: true, force: true })
  rmSync(unsafeDirectory, { recursive: true, force: true })
}
