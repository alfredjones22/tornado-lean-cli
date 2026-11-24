// Development oracle only. Runtime Lean code does not import or execute this.
import { readFileSync, writeFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { assertOracleIdentity, oracleSource } from './oracle-identity.mjs'

if (!process.env.TORNADO_NOTE_FIXTURE_TSX) {
  const result = spawnSync(process.execPath, ['--import', resolve(oracleSource, 'node_modules/tsx/dist/loader.mjs'),
    fileURLToPath(import.meta.url), ...process.argv.slice(2)],
  { stdio: 'inherit', env: { ...process.env, TORNADO_NOTE_FIXTURE_TSX: '1' } })
  process.exit(result.status ?? 1)
}
assertOracleIdentity()
const { SecretManager } = await import(pathToFileURL(resolve(oracleSource, 'node_modules/@kohaku-eth/tornado-cash/dist/index.js')))
const { encodeFunctionData, parseAbi, toHex } = await import(pathToFileURL(resolve(oracleSource, 'node_modules/viem/_esm/index.js')))
const { formatDepositBackup } = await import(pathToFileURL(resolve(oracleSource, 'src/domain/seed-bundle.ts')))
const packageJson = JSON.parse(readFileSync(resolve(oracleSource, 'node_modules/@kohaku-eth/tornado-cash/package.json')))
if (!['--write', '--check'].includes(process.argv[2])) throw new Error('Use --write or --check')
const emit = (file, output) => {
  if (process.argv[2] === '--write') writeFileSync(file, output)
  else if (readFileSync(file, 'utf8') !== output) throw new Error(`Pinned note fixture changed: ${file}`)
}

const pools = [
  { name: 'mainnet-eth-001', chainId: 1, denomination: '0.01', symbol: 'ETH',
    address: '0x199112Eb461ea7eeC1D75B33343542e1d069B41c', amount: 10n ** 16n, token: false,
    nullifierKey: '0x' + '00'.repeat(31) + '01', saltKey: '0x' + '00'.repeat(31) + '02' },
  { name: 'mainnet-wbtc-01', chainId: 1, denomination: '0.1', symbol: 'WBTC',
    address: '0x178169B423a011fff22B9e3F3abeA13414dDD0F1', amount: 10n ** 7n, token: true,
    nullifierKey: '0x' + 'a5'.repeat(32), saltKey: '0x' + '5a'.repeat(32) },
  { name: 'sepolia-eth-1', chainId: 11155111, denomination: '1', symbol: 'ETH',
    address: '0x8cc930096B4Df705A007c4A039BDFA1320Ed2508', amount: 10n ** 18n, token: false,
    nullifierKey: '0x' + 'ff'.repeat(32), saltKey: '0x' + '01'.repeat(32) },
]

const abi = parseAbi(['function deposit(bytes32 commitment) payable'])
const toLittleEndian31 = value => Array.from({ length: 31 }, (_, i) =>
  Number((value >> BigInt(i * 8)) & 255n).toString(16).padStart(2, '0')).join('')
const fixture = []
for (const pool of pools) {
  const manager = await SecretManager({ host: { keystore: {
    deriveAt: async path => {
      if (path.endsWith("/0'/0'")) return pool.nullifierKey
      if (path.endsWith("/1'/0'")) return pool.saltKey
      throw new Error(`Unexpected key path ${path}`)
    },
  } } })
  const secrets = await manager.getLegacyDepositSecrets({
    chainId: BigInt(pool.chainId), poolAddress: BigInt(pool.address), depositIndex: 0,
  })
  const preimage = toLittleEndian31(secrets.nullifier) + toLittleEndian31(secrets.salt)
  const commitment = toHex(secrets.commitment, { size: 32 })
  const nullifierHash = toHex(secrets.nullifierHash, { size: 32 })
  const uuidEntropy = '000102030405060708090a0b0c0d0e0f'
  fixture.push({
    name: pool.name, chainId: pool.chainId, denomination: pool.denomination,
    symbol: pool.symbol, address: pool.address, nullifierKey: pool.nullifierKey,
    saltKey: pool.saltKey, uuidEntropy,
    preimage, commitment, nullifierHash,
    raw: `tornado-${pool.symbol.toLowerCase()}-${pool.denomination}-${pool.chainId}-0x${preimage}`,
    depositCall: {
      to: pool.address,
      data: encodeFunctionData({ abi, functionName: 'deposit', args: [commitment] }),
      value: pool.token ? '0' : pool.amount.toString(),
    },
  })
}
emit(new URL('../fixtures/note-creation-vectors.json', import.meta.url),
  JSON.stringify({ sdkVersion: packageJson.version, vectors: fixture }, null, 2) + '\n')
const seeded = JSON.parse(readFileSync(new URL('../fixtures/seeded-note-vectors.json', import.meta.url)))
emit(new URL('../fixtures/seeded-backup-format.txt', import.meta.url),
  formatDepositBackup(seeded.groups[0].notes, seeded.mnemonic))
console.log(`Generated ${fixture.length} pinned SDK independent-note vectors.`)
