import { spawnSync } from 'node:child_process'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { assertOracleIdentity, oracleSource, repository } from './oracle-identity.mjs'

if (!process.env.TORNADO_COMPATIBILITY_TSX) {
  const result = spawnSync(process.execPath, ['--import', resolve(oracleSource, 'node_modules/tsx/dist/loader.mjs'),
    fileURLToPath(import.meta.url)],
  { stdio: 'inherit', env: { ...process.env, TORNADO_COMPATIBILITY_TSX: '1' } })
  process.exit(result.status ?? 1)
}
assertOracleIdentity()
const sourceModule = path => import(pathToFileURL(resolve(oracleSource, path)))
const { poolsFor } = await sourceModule('src/domain/catalog.ts')
const { requireDenominationPlan, denominationPlanChoices } = await sourceModule('src/domain/denomination-plan.ts')
const { readWithdrawalStatus } = await sourceModule('src/withdrawal/status-file.ts')
const rows = file => readFileSync(resolve(repository, file), 'utf8').trim().split('\n')
  .filter(line => !line.startsWith('#')).map(line => line.split(','))
const render = plan => plan.entries.map(({ pool, count }) => `${pool.denomination}:${count}`).join(';')
let grid = 0, choices = 0, statuses = 0
for (const [maskText, amount, status, expected] of rows('fixtures/plan-grid.csv')) {
  const mask = Number(maskText)
  const units = [1n, 3n, 10n, 30n, 100n].filter((_, index) => mask & (1 << index))
  const pools = poolsFor(1, 'ETH').filter(pool => units.includes(pool.amount / 10n ** 16n))
  let actual
  try { actual = ['ok', render(requireDenominationPlan(BigInt(amount) * 10n ** 16n, pools))] }
  catch { actual = ['error', ''] }
  if (actual[0] !== status || status === 'ok' && actual[1] !== expected)
    throw new Error(`Current oracle differs from historical plan grid at ${mask}/${amount}`)
  grid++
}
for (const [chain, symbol, amount, status, expected] of rows('fixtures/plan-choices.csv')) {
  let actual
  try { actual = ['ok', denominationPlanChoices(BigInt(amount), poolsFor(Number(chain), symbol)).map(render).join('|')] }
  catch { actual = ['error', ''] }
  if (actual[0] !== status || status === 'ok' && actual[1] !== expected)
    throw new Error(`Current oracle differs from historical plan choices at ${chain}/${symbol}/${amount}`)
  choices++
}
const directory = mkdtempSync(resolve(tmpdir(), 'tornado-public-status-oracle-'))
try {
  const file = resolve(directory, 'status.json')
  for (const row of JSON.parse(readFileSync(resolve(repository, 'fixtures/status-parity.json'), 'utf8')).cases) {
    writeFileSync(file, row.raw, { mode: 0o600 })
    let accepted = false
    try { await readWithdrawalStatus(file); accepted = true } catch {}
    if (accepted !== row.accepted) throw new Error(`Current status oracle changed: ${row.name}`)
    statuses++
  }
} finally { rmSync(directory, { recursive: true, force: true }) }
if (grid !== 1860 || choices !== 900 || statuses !== 38) throw new Error('Historical oracle case inventory changed')
console.log('PASS: alpha.40 revalidated 1860 plan grid, 900 plan choices and 38 historical status cases')
