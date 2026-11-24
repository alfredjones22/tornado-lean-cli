// Development-only pinned TypeScript/viem oracle; no network or transaction.
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { assertOracleIdentity, oracleCommit, oracleSource } from './oracle-identity.mjs'
if (!process.env.TORNADO_ABI_FIXTURE_TSX) {
  const result = spawnSync(process.execPath, ['--import', resolve(oracleSource, 'node_modules/tsx/dist/loader.mjs'),
    fileURLToPath(import.meta.url), ...process.argv.slice(2)],
  { stdio: 'inherit', env: { ...process.env, TORNADO_ABI_FIXTURE_TSX: '1' } })
  process.exit(result.status ?? 1)
}
assertOracleIdentity()
const sourceCalls = pathToFileURL(resolve(oracleSource, 'src/smart-account/calls.ts'))
const { parseContractCalls, callsHash } = await import(sourceCalls.href)

const target = '0x1111111111111111111111111111111111111111'
const address = '0x0000000000000000000000000000000000000000'
const checksum = '0x52908400098527886E0F7030069857D2E4169EE7'
const parameter = (name, type, components) => ({ name, type, ...(components ? { components } : {}) })
function method(inputs, values, { name = 'run', payable = false, value = '0', data = null } = {}) {
  return [{ to: target, value, data, contractMethod: { name, inputs, payable }, contractInputsValues: values }]
}
const cases = []
function add(name, input, chainId = 1) {
  const text = JSON.stringify(input)
  const calls = parseContractCalls(text, chainId)
  cases.push({ name, chainId, input, calls: calls.map(call => ({ ...call, value: String(call.value) })), callsHash: callsHash(calls) })
}
add('no-arguments', method([], {}))
add('transfer', method([parameter('to', 'address'), parameter('amount', 'uint256')], { to: address, amount: '1000000000000000001' }, { name: 'transfer' }))
add('aliases-and-safe-numbers', method([parameter('a', 'uint'), parameter('b', 'int'), parameter('c', 'uint64')], { a: '000001', b: -42, c: 9007199254740991 }))
const integerParts = [], integerValues = {}
for (let bits = 8; bits <= 256; bits += 8) {
  integerParts.push(parameter(`u${bits}`, `uint${bits}`), parameter(`i${bits}`, `int${bits}`))
  integerValues[`u${bits}`] = String(2n ** BigInt(bits) - 1n)
  integerValues[`i${bits}`] = String(-(2n ** BigInt(bits - 1)))
}
add('all-integer-width-boundaries', method(integerParts, integerValues))
const byteParts = [], byteValues = {}
for (let size = 1; size <= 32; size++) {
  byteParts.push(parameter(`b${size}`, `bytes${size}`)); byteValues[`b${size}`] = '0x' + 'ab'.repeat(size)
}
add('all-fixed-byte-widths', method(byteParts, byteValues))
add('booleans-and-checksum-address', method([parameter('a', 'bool'), parameter('b', 'bool'), parameter('c', 'bool'), parameter('d', 'address')], { a: true, b: 'false', c: false, d: checksum }))
add('dynamic-bytes-padding', method(['empty', 'a', 'b', 'c'].map(name => parameter(name, 'bytes')), { empty: '0x', a: '0x' + '01'.repeat(31), b: '0x' + '02'.repeat(32), c: '0x' + '03'.repeat(33) }))
add('unicode-strings', method([parameter('empty', 'string'), parameter('message', 'string')], { empty: '', message: 'Zagreb 🌪️ / Ελληνικά / 日本語' }))
add('dynamic-integer-array-json', method([parameter('values', 'uint16[]')], { values: '[0,1,"65535"]' }))
add('fixed-integer-array', method([parameter('values', 'int8[3]')], { values: [-128, '0', 127] }))
add('nested-fixed-array', method([parameter('values', 'uint32[2][2]')], { values: [[1, 2], [3, 4]] }))
add('ragged-dynamic-arrays', method([parameter('values', 'uint256[][]')], { values: [[], [1], ['2', '3']] }))
add('fixed-array-of-dynamic-arrays', method([parameter('values', 'uint[][2]')], { values: [[1, 2], []] }))
add('dynamic-array-of-fixed-arrays', method([parameter('values', 'uint[2][]')], { values: [[1, 2], [3, 4]] }))
add('fixed-array-of-bytes', method([parameter('values', 'bytes2[2]')], { values: ['0xabcd', '0x1234'] }))
const staticParts = [parameter('owner', 'address'), parameter('count', 'uint64'), parameter('enabled', 'bool')]
add('static-tuple-positional', method([parameter('config', 'tuple', staticParts)], { config: [checksum, '42', 'true'] }))
add('static-tuple-named-json', method([parameter('config', 'tuple', staticParts)], { config: JSON.stringify({ owner: address, count: 0, enabled: false }) }))
const dynamicParts = [parameter('message', 'string'), parameter('numbers', 'int16[]'), parameter('blob', 'bytes')]
add('dynamic-tuple-named', method([parameter('config', 'tuple', dynamicParts)], { config: { message: 'hello', numbers: [-1, 2], blob: '0xabcdef' } }))
add('dynamic-tuple-array', method([parameter('rows', 'tuple[]', dynamicParts)], { rows: [{ message: '', numbers: [], blob: '0x' }, ['world', [3, -4], '0x00']] }))
add('fixed-dynamic-tuple-array', method([parameter('rows', 'tuple[2]', dynamicParts)], { rows: [['a', [1], '0x'], ['b', [], '0x1234']] }))
const nestedParts = [parameter('fixed', 'tuple', staticParts), parameter('dynamic', 'tuple', dynamicParts), parameter('labels', 'string[]')]
add('nested-tuples-and-strings', method([parameter('root', 'tuple', nestedParts)], { root: { fixed: [address, '9', true], dynamic: ['x', [-2, 3], '0xff'], labels: ['one', '', 'three'] } }))
add('empty-compounds', method([parameter('a', 'uint[]'), parameter('b', 'tuple', []), parameter('c', 'tuple[]', [])], { a: [], b: [], c: [[], []] }))
add('maximum-sized-empty-tuple-array', method([parameter('rows', 'tuple[]', [])], { rows: Array.from({ length: 1024 }, () => []) }))
add('near-calldata-byte-bound', method([parameter('rows', 'uint8[]')], { rows: Array(509).fill(255) }))
let deepest = '1'; for (let i = 0; i < 12; i++) deepest = [deepest]
add('maximum-nesting-depth', method([parameter('value', 'uint' + '[]'.repeat(12))], { value: deepest }))
add('payable-method', method([parameter('amount', 'uint256')], { amount: '5' }, { payable: true, value: '1' }))
const matched = method([parameter('amount', 'uint256')], { amount: '7' })
matched[0].data = parseContractCalls(JSON.stringify(matched), 1)[0].data.toUpperCase()
add('matching-provided-calldata', matched)
add('safe-v1-wrapper', { version: '1.0', chainId: '11155111', transactions: method([parameter('value', 'string')], { value: 'sepolia' }) }, 11155111)

const rejectionCases = []
function reject(name, input, chainId = 1) {
  let rejected = false
  try { parseContractCalls(JSON.stringify(input), chainId) } catch { rejected = true }
  if (!rejected) throw new Error(`Oracle unexpectedly accepted ${name}`)
  rejectionCases.push({ name, chainId, input })
}
for (const [name, type, value] of [
  ['uint-negative', 'uint8', '-1'], ['uint-overflow', 'uint8', '256'],
  ['int-overflow', 'int8', '128'], ['int-underflow', 'int8', '-129'],
  ['unsafe-number', 'uint256', 9007199254740992], ['fractional-number', 'uint256', 1.5],
  ['hex-integer', 'uint256', '0x10'], ['wrong-boolean', 'bool', 'TRUE'],
  ['fixed-bytes-size', 'bytes2', '0xff'], ['bad-address', 'address', '0x1234'],
  ['wrong-array-length', 'uint8[2]', [1]],
  ['long-array', 'uint8[]', Array(1025).fill(0)], ['tuple-missing-component', 'tuple', []],
]) reject(name, method([parameter('value', type, type === 'tuple' ? [parameter('x', 'uint')] : undefined)], { value }))
reject('missing-argument', method([parameter('value', 'uint')], {}))
reject('nonpayable-value', method([], {}, { value: '1' }))
reject('calldata-disagreement', method([], {}, { data: '0x' }))
const delegated = method([], {}); delegated[0].operation = '1'; reject('delegatecall', delegated)
let nested = '1'; for (let i = 0; i < 13; i++) nested = [nested]
reject('nested-depth-limit', method([parameter('value', 'uint' + '[]'.repeat(13))], { value: nested }))
reject('wrong-safe-chain', { version: '1.0', chainId: '11155111', transactions: method([], {}) })
reject('calldata-byte-bound', method([parameter('rows', 'uint8[]')], { rows: Array(510).fill(255) }))

const sha256 = bytes => createHash('sha256').update(bytes).digest('hex')
const output = { sourceCommit: oracleCommit, viemVersion: '2.55.19',
  sourceCallsSha256: sha256(readFileSync(sourceCalls)),
  cases, rejectionCases }
const fixture = new URL('../fixtures/imported-abi-vectors.json', import.meta.url)
const encoded = JSON.stringify(output, null, 2) + '\n'
if (process.argv[2] === '--write') writeFileSync(fixture, encoded)
else if (process.argv[2] !== '--check' || readFileSync(fixture, 'utf8') !== encoded)
  throw new Error('Use --write or --check; imported ABI oracle fixture must match')
console.log(`Generated ${cases.length} imported ABI parity cases and ${rejectionCases.length} rejection cases.`)
