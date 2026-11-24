import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { assertOracleIdentity, oracleCommit } from './oracle-identity.mjs'

// Differential check for the local read-only commands and root version flags.
// The TypeScript oracle must be the clean, frozen source and its known build.
const root = fileURLToPath(new URL('../', import.meta.url))
const cli = resolve(process.env.TORNADO_TS_CLI ?? resolve(root, '../tornado-cli-new-era'))
const expectedCommit = oracleCommit
const expectedDistHash = 'cb039416616458ab261036e08e3c4d83991a1b6d7ab4259328894292c035f809'
const leanBin = resolve(root, '.lake/build/bin/tornado')
const reportPath = resolve(root, 'reports/parity.json')
const cases = JSON.parse(readFileSync(resolve(root, 'fixtures/parity-read-only.json'), 'utf8'))
const digests = JSON.parse(readFileSync(resolve(root, 'fixtures/parity-oracle-digests.json'), 'utf8'))
const fail = message => { throw new Error(message) }
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex')
const checked = (ok, message) => { if (!ok) fail(message) }
const env = { ...process.env, LEAN_TOOLCHAIN: 'leanprover/lean4:v4.29.1',
  NO_COLOR: '1', CI: '1', TZ: 'UTC' }
delete env.TORNADO_RPC_URL
delete env.TORNADO_BUNDLER_URL
const identity = assertOracleIdentity(cli)

function run(executable, args, cwd, timeout = 15000) {
  const result = spawnSync(executable, args, { cwd, env, encoding: 'utf8', timeout,
    maxBuffer: 1024 * 1024 })
  if (result.error) fail(`${executable}: ${result.error.message}`)
  checked(result.signal === null, `${executable} terminated by ${result.signal}`)
  return { exitCode: result.status, stdout: result.stdout, stderr: result.stderr }
}

const [nodeMajor, nodeMinor] = process.versions.node.split('.').map(Number)
checked(nodeMajor > 22 || nodeMajor === 22 && nodeMinor >= 18,
  'Run parity with Node 22.18 or newer')
checked(cases.schemaVersion === 1 && Array.isArray(cases.cases) && cases.cases.length > 0,
  'Invalid parity fixture')
checked(process.argv.includes('--write-oracle') || digests.schemaVersion === 1 && digests.sourceCommit === expectedCommit &&
  Object.keys(digests.cases).length === cases.cases.length,
  'Invalid frozen oracle digest fixture')
checked(new Set(cases.cases.map(row => row.name)).size === cases.cases.length,
  'Duplicate parity case name')
for (const row of cases.cases) {
  checked(typeof row.name === 'string' && Array.isArray(row.args) &&
    row.args.every(arg => typeof arg === 'string') &&
    ['success', 'failure'].includes(row.expect) &&
    (row.args[0] === 'pools' || row.args[0] === 'deposit' && row.args[1] === 'plan' ||
      row.args.length === 1 && ['--version', '-V'].includes(row.args[0])),
  `Invalid or non-read-only parity case: ${row.name}`)
}
const commit = run('git', ['rev-parse', 'HEAD'], cli).stdout.trim()
const dirt = run('git', ['status', '--porcelain=v1'], cli).stdout.trim()
checked(commit === expectedCommit && !dirt, 'TypeScript oracle is not the clean frozen CLI commit')
const dist = resolve(cli, 'dist/index.js')
checked(existsSync(dist) && sha256(readFileSync(dist)) === expectedDistHash,
  'TypeScript oracle dist/index.js is missing or differs from the frozen build')
if (!process.argv.includes('--write-oracle') && !process.argv.includes('--skip-build')) {
  const build = run('lake', ['build', 'tornado'], root, 120000)
  checked(build.exitCode === 0 && existsSync(leanBin), `Lean CLI build failed:\n${build.stderr || build.stdout}`)
}

const results = []
const regenerated = {}
for (const row of cases.cases) {
  const oracle = run(process.execPath, [resolve(cli, 'bin/tornado.mjs'), ...row.args], cli)
  checked((row.expect === 'success') === (oracle.exitCode === 0),
    `Frozen oracle changed outcome for ${row.name}: ${oracle.stderr}`)
  const digest = sha256(`${oracle.exitCode}\0${oracle.stdout}\0${oracle.stderr}`)
  regenerated[row.name] = digest
  if (process.argv.includes('--write-oracle')) continue
  checked(digest === digests.cases[row.name],
    `Frozen oracle output differs from pinned fixture for ${row.name}`)
  const lean = run(leanBin, row.args, root)
  const matches = lean.exitCode === oracle.exitCode && lean.stdout === oracle.stdout &&
    lean.stderr === oracle.stderr
  results.push({ name: row.name, args: row.args, expect: row.expect,
    status: matches ? 'MATCH' : 'MISMATCH', oracle, lean })
}
if (process.argv.includes('--write-oracle')) {
  writeFileSync(resolve(root, 'fixtures/parity-oracle-digests.json'),
    JSON.stringify({ schemaVersion: 1, sourceCommit: expectedCommit, cases: regenerated }, null, 2) + '\n')
  console.log(`Regenerated ${cases.cases.length} alpha.40 read-only oracle digests`)
  process.exit(0)
}
const matched = results.filter(row => row.status === 'MATCH').length
const report = { schemaVersion: 1, sourceCommit: expectedCommit,
  runId: process.env.TORNADO_VERIFY_RUN_ID ?? null,
  sourceBuildSHA256: expectedDistHash, leanToolchain: env.LEAN_TOOLCHAIN,
  sourceLockSHA256: identity.files['package-lock.json'],
  sourceSdkTreeSHA256: identity.packages['node_modules/@kohaku-eth/tornado-cash'].sha256,
  fixtureSHA256: sha256(readFileSync(resolve(root, 'fixtures/parity-read-only.json'))),
  oracleDigestFixtureSHA256: sha256(readFileSync(resolve(root, 'fixtures/parity-oracle-digests.json'))),
  status: matched === results.length ? 'PASS' : 'FAIL', total: results.length, matched, cases: results }
mkdirSync(dirname(reportPath), { recursive: true })
writeFileSync(reportPath, JSON.stringify(report, null, 2) + '\n')
console.log(`Read-only CLI parity: ${matched}/${results.length} cases matched exactly`)
if (report.status !== 'PASS') {
  for (const row of results.filter(row => row.status === 'MISMATCH')) {
    console.error(`MISMATCH ${row.name} ${JSON.stringify(row.args)}`)
    console.error(`  TS:   ${JSON.stringify(row.oracle)}`)
    console.error(`  Lean: ${JSON.stringify(row.lean)}`)
  }
  process.exitCode = 1
}
