import { readFileSync, writeFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { resolve, dirname } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

// Development-only public roots from the exact MiMC tree package used by the
// pinned alpha.38 CLI. The native Lean runtime does not load this package.
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const source = process.env.TORNADO_TS_CLI ?? resolve(root, '../tornado-cli-new-era')
const expectedCommit = 'daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7'
const commit = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: source, encoding: 'utf8' }).trim()
if (commit !== expectedCommit) throw Error('Pinned CLI commit changed')
const sdk = JSON.parse(readFileSync(resolve(source, 'node_modules/@kohaku-eth/tornado-cash/package.json')))
const mimc = JSON.parse(readFileSync(resolve(source, 'node_modules/@kohaku-eth/mimc-tree/package.json')))
if (sdk.version !== '0.1.0-alpha.38' || mimc.version !== '0.0.3')
  throw Error('Pinned Tornado SDK/MiMC tree package changed')
const module = await import(pathToFileURL(resolve(source, 'node_modules/@kohaku-eth/mimc-tree/dist/index.js')).href)
const cases = [[], ['1'], ['1', '2'], ['1', '3'], ['1', '2', '3'], ['1', '2', '3', '4']]
const fixture = {
  schemaVersion: 1,
  sourceCommit: commit,
  tornadoSdkVersion: sdk.version,
  mimcTreeVersion: mimc.version,
  roots: cases.map(leaves => ({ leaves, root: module.computeMimcMerkleTreeRoot(leaves).toString() })),
}
const encoded = JSON.stringify(fixture, null, 2) + '\n'
const file = resolve(root, 'fixtures/history-reducer-vectors.json')
if (process.argv.includes('--check')) {
  if (readFileSync(file, 'utf8') !== encoded) throw Error('Pinned MiMC history root vectors changed')
  console.log('PASS: six pinned SDK MiMC pool-root vectors')
} else {
  writeFileSync(file, encoded)
  console.log('Wrote six pinned SDK MiMC pool-root vectors')
}
