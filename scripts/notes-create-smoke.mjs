import { spawnSync } from 'node:child_process'
import { chmodSync, mkdtempSync, readFileSync, rmSync, statSync } from 'node:fs'
import { join, relative, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const tsRoot = resolve(process.env.TORNADO_TS_CLI ?? resolve(root, '../tornado-cli-new-era'))
const native = resolve(root, '.lake/build/bin/tornado')
const ts = resolve(tsRoot, 'bin/tornado.mjs')
const testRoot = mkdtempSync(join(root, '.notes-create-test-'))
const run = (binary, args, cwd, timeout = 60000, env = process.env) => {
  const result = spawnSync(binary, args, { cwd, env, encoding: 'utf8', timeout,
    maxBuffer: 1024 * 1024 })
  if (result.error || result.signal) throw result.error ?? new Error(`${binary} terminated`)
  return result
}
const noteStrings = backup => backup.match(/tornado-[a-z0-9]+-[\d.]+-\d+-0x[\da-f]{124}/g) ?? []
const compareInspect = path => {
  const args = ['notes', 'inspect', '--file', path, '--chain', '1']
  const lean = run(native, args, root)
  const oracle = run(process.execPath, [ts, ...args], tsRoot)
  if (lean.status !== 0 || oracle.status !== 0 || lean.stdout !== oracle.stdout) {
    throw new Error('Generated note commitments differ from the pinned CLI')
  }
}
const ensurePrivate = path => {
  if ((statSync(path).mode & 0o777) !== 0o600) {
    throw new Error('New note backup is not mode 0600')
  }
}
try {
  chmodSync(testRoot, 0o700)
  const independent = join(testRoot, 'independent.notes')
  const created = run(native, ['notes', 'create', '--denom', '0.01', '--count', '2',
    '--out', independent], root, 120000)
  if (created.status !== 0 || created.stdout.includes('tornado-eth-') ||
      noteStrings(readFileSync(independent, 'utf8')).length !== 2) {
    throw new Error(`Independent note creation failed: ${created.stderr}`)
  }
  ensurePrivate(independent)
  compareInspect(independent)
  const before = readFileSync(independent)
  const repeated = run(native, ['notes', 'create', '--denom', '0.01', '--count', '2',
    '--out', independent], root, 120000)
  if (repeated.status === 0 || !readFileSync(independent).equals(before)) {
    throw new Error('Exclusive note backup creation failed')
  }

  const seeded = join(testRoot, 'seeded.notes')
  const session = run(native, ['notes', 'create', '--denom', '0.01', '--count', '2',
    '--seed-bundle', '--out', seeded], root, 180000)
  const seededText = readFileSync(seeded, 'utf8')
  const phrase = seededText.match(/SEED PHRASE \(SECRET\) --------\n([^\n]+)\n/)?.[1]
  if (session.status !== 0 || !phrase || phrase.split(' ').length !== 24 ||
      noteStrings(seededText).length !== 2 || session.stdout.includes(phrase)) {
    throw new Error(`Seeded note session creation failed: ${session.stderr}`)
  }
  ensurePrivate(seeded)
  compareInspect(seeded)
  const oracleCode = `
    import { readFileSync } from 'node:fs';
    import { deriveSeededDepositNotes } from './src/domain/seed-bundle.ts';
    import { poolFor } from './src/domain/catalog.ts';
    const text = readFileSync(process.argv[1], 'utf8');
    const phrase = text.match(/SEED PHRASE \\(SECRET\\) --------\\n([^\\n]+)\\n/)?.[1];
    const raw = text.match(/tornado-[a-z0-9]+-[\\d.]+-\\d+-0x[\\da-f]{124}/g) ?? [];
    const pools = raw.map(note => { const parts = note.split('-'); return poolFor(1, parts[2], parts[1]); });
    const derived = await deriveSeededDepositNotes(pools, phrase);
    if (derived.length !== raw.length || derived.some((note, i) => note.raw !== raw[i])) process.exit(1);
    console.log('seeded derivation matched');
  `
  const recovered = run(process.execPath, ['--import', 'tsx', '--input-type=module',
    '-e', oracleCode, seeded], tsRoot, 180000)
  if (recovered.status !== 0 || recovered.stdout.trim() !== 'seeded derivation matched') {
    throw new Error(`Seed-session recovery differs from pinned SDK: ${recovered.stderr}`)
  }

  const planned = join(testRoot, 'planned.notes')
  const plan = run(native, ['notes', 'create-plan', '--amount', '1.01', '--out', planned],
    root, 180000)
  if (plan.status !== 0 || noteStrings(readFileSync(planned, 'utf8')).length !== 2) {
    throw new Error(`Planned note creation failed: ${plan.stderr}`)
  }
  ensurePrivate(planned)
  compareInspect(planned)

  const plannedSeeded = join(testRoot, 'planned-seeded.notes')
  const planSession = run(native, ['notes', 'create-plan', '--amount', '1.01',
    '--seed-bundle', '--out', plannedSeeded], root, 180000)
  if (planSession.status !== 0 || noteStrings(readFileSync(plannedSeeded, 'utf8')).length !== 2) {
    throw new Error(`Seeded plan creation failed: ${planSession.stderr}`)
  }
  ensurePrivate(plannedSeeded)
  compareInspect(plannedSeeded)
  const recoveredPlan = run(process.execPath, ['--import', 'tsx', '--input-type=module',
    '-e', oracleCode, plannedSeeded], tsRoot, 180000)
  if (recoveredPlan.status !== 0 || recoveredPlan.stdout.trim() !== 'seeded derivation matched') {
    throw new Error(`Seeded plan recovery differs from pinned SDK: ${recoveredPlan.stderr}`)
  }

  const relativePath = `./${relative(root, testRoot)}/relative.notes`
  const relativeCreate = run(native, ['notes', 'create', '--denom', '0.01',
    '--out', relativePath], root, 120000)
  if (relativeCreate.status !== 0) throw new Error(`Relative private path failed: ${relativeCreate.stderr}`)
  ensurePrivate(join(testRoot, 'relative.notes'))
  console.log('Native note creation: independent, seeded recovery, both plan modes, relative path, and exclusive backup checks passed')
} finally {
  rmSync(testRoot, { recursive: true, force: true })
}
