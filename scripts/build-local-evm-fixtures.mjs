// Local, offline compiler inputs. No remote RPC, package install, or signing.
import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

export const repository = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const pinCommit = '1b23e91a06fb4af50220507febf38bd05078e6a4'
const aaCommit = '4cbc06072cdc19fd60f285c5997f4f7f57a588de'
const ozCommit = '5fd1781b1454fd1ef8e722282f86f9293cacf256'
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const run = (command, args, cwd) => execFileSync(command, args, { cwd, encoding: 'utf8',
  env: { ...process.env, FOUNDRY_DISABLE_NIGHTLY_WARNING: '1' }, stdio: ['ignore', 'pipe', 'pipe'] }).trim()
const readJson = path => JSON.parse(readFileSync(path, 'utf8'))
const strip = hex => hex.replace(/^0x/, '')

function requireRevision(path, expected) {
  const actual = run('git', ['rev-parse', 'HEAD'], path)
  if (actual !== expected) throw new Error(`Source revision differs at ${path}: ${actual}; expected ${expected}`)
}

function artifact(path) {
  const full = readJson(path)
  const metadata = typeof full.metadata === 'string' ? JSON.parse(full.metadata) : full.metadata
  return { abi: full.abi, bytecode: full.bytecode.object, runtime: full.deployedBytecode.object, metadata }
}

export function buildLocalEvmFixtures() {
  const contracts = process.env.TORNADO_EVM_CONTRACTS_SOURCE || resolve(repository, '../kohaku-contracts/privacy-paymaster')
  requireRevision(contracts, pinCommit)
  requireRevision(join(contracts, 'lib/account-abstraction'), aaCommit)
  requireRevision(join(contracts, 'lib/openzeppelin-contracts'), ozCommit)
  const temporary = mkdtempSync(join(tmpdir(), 'tornado-lean-evm-'))
  try {
    const modern = join(temporary, 'modern')
    const classic = join(temporary, 'classic')
    for (const path of [modern, classic]) mkdirSync(join(path, 'src'), { recursive: true })
    copyFileSync(join(repository, 'tests/evm/IntegrationHarness.sol'), join(modern, 'src/IntegrationHarness.sol'))
    copyFileSync(join(repository, 'tests/evm/DepositHarness.sol'), join(modern, 'src/DepositHarness.sol'))
    const remappings = [
      `privacy/=${contracts}/`,
      `@account-abstraction/=${contracts}/lib/account-abstraction/`,
      `@openzeppelin/=${contracts}/lib/openzeppelin-contracts/`,
      `@uniswap/v3-core/=${contracts}/lib/v3-core/`,
      `@uniswap/v3-periphery/=${contracts}/lib/v3-periphery/`,
    ]
    writeFileSync(join(modern, 'foundry.toml'), `[profile.default]\nsrc = "src"\nout = "out"\nsolc_version = "0.8.28"\nevm_version = "cancun"\noptimizer = true\noptimizer_runs = 200\nbytecode_hash = "none"\nallow_paths = [${JSON.stringify(contracts)}]\nremappings = ${JSON.stringify(remappings)}\n`)
    copyFileSync(join(repository, 'fixtures/tornado-classic-Verifier.sol'), join(classic, 'src/Verifier.sol'))
    writeFileSync(join(classic, 'foundry.toml'), '[profile.default]\nsrc = "src"\nout = "out"\nsolc_version = "0.7.6"\nevm_version = "istanbul"\noptimizer = true\noptimizer_runs = 200\nbytecode_hash = "none"\n')
    for (const path of [classic, modern]) run('forge', ['build', '--offline'], path)
    const definitions = {
      Verifier: [classic, 'Verifier.sol', 'MIT'],
      SimpleAccount: [modern, 'SimpleAccount.sol', 'MIT'],
      SimpleAccountFactory: [modern, 'SimpleAccountFactory.sol', 'MIT'],
      TornadoPaymaster: [modern, 'TornadoPaymaster.sol', 'UNLICENSED; locally compiled only'],
      ProbeEntryPoint: [modern, 'IntegrationHarness.sol', 'MIT; synthetic test boundary'],
      ProbeToken: [modern, 'IntegrationHarness.sol', 'MIT; synthetic token'],
      ProbePool: [modern, 'IntegrationHarness.sol', 'MIT; synthetic pool, no proof checks'],
      ProbeRecorder: [modern, 'IntegrationHarness.sol', 'MIT; test observer'],
      ProbeFailure: [modern, 'IntegrationHarness.sol', 'MIT; intentional revert'],
      ProbeEthPool: [modern, 'IntegrationHarness.sol', 'MIT; synthetic single-root ETH ledger, actual Classic verifier'],
      ProbeDepositToken: [modern, 'DepositHarness.sol', 'MIT; synthetic allowance-reset test token'],
      ProbeDepositPool: [modern, 'DepositHarness.sol', 'MIT; synthetic deposit-only ledger'],
    }
    const artifacts = {}
    const compiled = {}
    const sources = new Map()
    for (const [name, [directory, source, license]] of Object.entries(definitions)) {
      const current = artifact(join(directory, 'out', source, `${name}.json`))
      artifacts[name] = current
      compiled[name] = {
        compiler: current.metadata.compiler.version,
        evmVersion: current.metadata.settings.evmVersion,
        optimizer: current.metadata.settings.optimizer,
        bytecodeHash: current.metadata.settings.metadata.bytecodeHash,
        creationSHA256: sha(Buffer.from(strip(current.bytecode), 'hex')),
        unpatchedRuntimeSHA256: sha(Buffer.from(strip(current.runtime), 'hex')),
        license,
      }
      for (const key of Object.keys(current.metadata.sources)) {
        let absolute, label
        if (key === 'src/Verifier.sol') {
          absolute = join(repository, 'fixtures/tornado-classic-Verifier.sol'); label = 'repo/fixtures/tornado-classic-Verifier.sol'
        } else if (key === 'src/IntegrationHarness.sol') {
          absolute = join(repository, 'tests/evm/IntegrationHarness.sol'); label = 'repo/tests/evm/IntegrationHarness.sol'
        } else if (key === 'src/DepositHarness.sol') {
          absolute = join(repository, 'tests/evm/DepositHarness.sol'); label = 'repo/tests/evm/DepositHarness.sol'
        } else {
          absolute = key.startsWith('/') ? key : resolve(directory, key)
          if (!absolute.startsWith(contracts + '/')) throw new Error(`Unexpected compiler source: ${key}`)
          label = 'privacy-paymaster/' + absolute.slice(contracts.length + 1)
        }
        sources.set(label, sha(readFileSync(absolute)))
      }
    }
    const manifest = {
      schema: 1,
      scope: 'Local actual Classic verifier and AA account/factory/paymaster; synthetic EntryPoint, token and pool. No full handleOps or real pool integration.',
      sourceRevisions: { privacyPaymaster: pinCommit, accountAbstraction: aaCommit, openzeppelin: ozCommit },
      contracts: compiled,
      sourcesSHA256: Object.fromEntries([...sources].sort(([a], [b]) => a.localeCompare(b))),
      fixturesSHA256: Object.fromEntries(['fixtures/simple7702-code.json', 'fixtures/seeded-backup-format.txt',
        'fixtures/seeded-note-vectors.json'].map(path => [path, sha(readFileSync(join(repository, path)))])),
    }
    return { temporary, artifacts, manifest, cleanup: () => rmSync(temporary, { recursive: true, force: true }) }
  } catch (error) {
    rmSync(temporary, { recursive: true, force: true })
    throw error
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const built = buildLocalEvmFixtures()
  try {
    const destination = join(repository, 'fixtures/evm/artifact-provenance.json')
    if (process.argv.includes('--pin')) {
      mkdirSync(dirname(destination), { recursive: true })
      writeFileSync(destination, JSON.stringify(built.manifest, null, 2) + '\n')
      console.log('Pinned local EVM compiler/source/bytecode hashes.')
    } else {
      const expected = readJson(destination)
      if (JSON.stringify(expected) !== JSON.stringify(built.manifest)) throw new Error('Local EVM provenance differs from the pinned fixture.')
      console.log('PASS: local EVM provenance reproduced offline.')
    }
  } finally { built.cleanup() }
}
