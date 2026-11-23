#!/usr/bin/env node
// Public development fixture from the exact pinned TypeScript CLI journal
// constructor. Run with Node 22: node scripts/deposit-status-source-check.mjs --check.
import { execFileSync, spawnSync } from 'node:child_process'
import { readFileSync, writeFileSync } from 'node:fs'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { dirname, join, resolve } from 'node:path'

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const source = resolve(root, '../tornado-cli-new-era')
if (!process.env.TORNADO_DEPOSIT_FIXTURE_TSX) {
  const result = spawnSync(process.execPath,
    ['--import', join(source, 'node_modules/tsx/dist/loader.mjs'),
      fileURLToPath(import.meta.url), ...process.argv.slice(2)],
    { stdio: 'inherit', env: { ...process.env, TORNADO_DEPOSIT_FIXTURE_TSX: '1' } })
  process.exit(result.status ?? 1)
}
const expectedCommit = 'daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7'
const head = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: source, encoding: 'utf8' }).trim()
if (head !== expectedCommit) throw new Error('TypeScript CLI source revision changed')
const dirty = execFileSync('git', ['status', '--porcelain', '--untracked-files=no'],
  { cwd: source, encoding: 'utf8' }).trim()
if (dirty) throw new Error('TypeScript CLI source checkout has tracked changes')
const { makeDepositJournal } = await import(pathToFileURL(join(source, 'src/storage/deposit-journal.ts')).href)
const { poolFor } = await import(pathToFileURL(join(source, 'src/domain/catalog.ts')).href)
const pool = poolFor(1, '0.01', 'ETH')
if (!pool) throw new Error('Pinned 0.01 ETH pool missing')
const commitment = `0x${'aa'.repeat(32)}`
const transactionHash = `0x${'97'.repeat(32)}`
const step = { kind: 'deposit', label: 'Deposit 0.01 ETH', to: pool.address,
  data: '0x', value: 0n, note: { pool, commitment } }
const journal = makeDepositJournal([step], 1,
  '0x52908400098527886E0F7030069857D2E4169EE7')
journal.createdAt = '2026-11-22T00:00:00.000Z'
journal.steps[0].status = 'prepared'
journal.steps[0].hash = transactionHash
const output = JSON.stringify(journal, null, 2) + '\n'
const fixture = join(root, 'fixtures/deposit-status-journal.json')
if (process.argv[2] === '--write') {
  writeFileSync(fixture, output)
  console.log('Wrote pinned sequential deposit journal fixture')
} else if (process.argv[2] === '--check') {
  if (readFileSync(fixture, 'utf8') !== output)
    throw new Error('Sequential deposit journal differs from pinned TypeScript output')
  console.log('PASS: pinned TypeScript sequential deposit journal fixture')
} else throw new Error('Use --write or --check')
