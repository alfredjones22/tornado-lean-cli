import { readFileSync, writeFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { execFileSync } from 'node:child_process'
import { resolve } from 'node:path'
import { assertOracleIdentity, oracleCommit, oracleSource } from './oracle-identity.mjs'

// Development-only public toy setup. Its toxic scalars are deliberately
// public; it must never be reused as a production ceremony or proving key.
const repository = fileURLToPath(new URL('../', import.meta.url))
const source = oracleSource
const sourceCommit = oracleCommit
assertOracleIdentity(source)
if (execFileSync('git', ['-C', source, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim() !== sourceCommit)
  throw new Error('The pinned TypeScript oracle checkout moved')
const micro = resolve(source, 'node_modules/micro-zk-proofs')
const version = path => JSON.parse(readFileSync(path, 'utf8')).version
if (version(`${micro}/package.json`) !== '0.3.1' ||
    version(`${micro}/node_modules/@noble/curves/package.json`) !== '2.2.0')
  throw new Error('Pinned independent oracle version changed')
const { buildSnark } = await import(pathToFileURL(`${micro}/index.js`).href)
const { bn254 } = await import(pathToFileURL(`${micro}/node_modules/@noble/curves/bn254.js`).href)
const Fr = bn254.fields.Fr
const snark = buildSnark(bn254, { nqr: 7 })
const circuit = {
  nVars: 3, nPubInputs: 1, nOutputs: 0,
  constraints: [[{ 2: '1' }, { 2: '1' }, { 1: '1' }]],
}
function draws(values) {
  let index = 0
  const read = size => {
    if (size !== 32 || index >= values.length) throw new Error('Unexpected oracle draw')
    const bytes = new Uint8Array(32)
    let value = values[index++]
    for (let i = 31; i >= 0; i--) { bytes[i] = Number(value & 255n); value >>= 8n }
    if (value !== 0n) throw new Error('Oversized fixture scalar')
    return bytes
  }
  return { read, check: () => {
    if (index !== values.length) throw new Error('Unused oracle draw')
  } }
}
const toxic = [17n, 5n, 7n, 11n, 13n]
const setupDraws = draws(toxic)
const setup = snark.groth.setup(circuit, setupDraws.read)
setupDraws.check()
const witness = [1n, 49n, 7n]
const blinding = [19n, 23n]
const proofDraws = draws(blinding)
const result = await snark.groth.createProof(setup.pkey, witness, proofDraws.read)
proofDraws.check()
if (!snark.groth.verifyProof(setup.vkey, result)) throw new Error('Toy circuit oracle failed')
if (snark.groth.verifyProof(setup.vkey, { ...result, publicSignals: [50n] }))
  throw new Error('Changed toy public signal was accepted')

// Independent O(n^2) inverse DFT and schoolbook product, not the oracle's
// FFT implementation. Include the setup's public-input padding rows.
const n = setup.pkey.domainSize
const root = Fr.pow(7n, (Fr.ORDER - 1n) / BigInt(n))
const evaluate = polynomials => {
  const out = new Array(n).fill(0n)
  polynomials.forEach((polynomial, index) => {
    for (const [row, coefficient] of Object.entries(polynomial))
      out[Number(row)] = Fr.add(out[Number(row)], Fr.mul(witness[index], coefficient))
  })
  return out
}
const inverseDFT = values => values.map((_, k) => {
  let sum = 0n
  for (let j = 0; j < n; j++)
    sum = Fr.add(sum, Fr.mul(values[j], Fr.pow(root, BigInt((n - j * k % n) % n))))
  return Fr.mul(sum, Fr.inv(BigInt(n)))
})
const a = inverseDFT(evaluate(setup.pkey.polsA))
const b = inverseDFT(evaluate(setup.pkey.polsB))
const product = new Array(2 * n).fill(0n)
for (let i = 0; i < n; i++) for (let j = 0; j < n; j++)
  product[i + j] = Fr.add(product[i + j], Fr.mul(a[i], b[j]))
const h = product.slice(n)
while (h.length && h.at(-1) === 0n) h.pop()
const point = result.proof
const limbs = [point.pi_a[0], point.pi_a[1], point.pi_b[0][1], point.pi_b[0][0],
  point.pi_b[1][1], point.pi_b[1][0], point.pi_c[0], point.pi_c[1]]
const fixture = {
  schemaVersion: 1,
  profile: 'Public toy x*x=y; 1 public input; test-only setup with disclosed toxic scalars',
  oracle: 'micro-zk-proofs@0.3.1 / @noble/curves@2.2.0 BN254 / NQR 7',
  oracleSourceSHA256: createHash('sha256').update(readFileSync(`${micro}/index.js`)).digest('hex'),
  circuit, toxic: { t: toxic[0], alpha: toxic[1], beta: toxic[2], gamma: toxic[3], delta: toxic[4] },
  witness, blindingR: blinding[0], blindingS: blinding[1],
  provingKey: setup.pkey, verifyingKey: setup.vkey,
  publicSignals: result.publicSignals, proof: result.proof, h,
  solidityProofHex: '0x' + limbs.map(x => x.toString(16).padStart(64, '0')).join(''),
  valid: true, changedPublicSignal: '50', changedPublicSignalValid: false,
}
const output = JSON.stringify(fixture,
  (_, value) => typeof value === 'bigint' ? String(value) : value, 2) + '\n'
const fixturePath = resolve(repository, 'packages/lean-crypto/fixtures/small-circuit-vectors.json')
if (process.argv.length !== 3 || !['--write', '--check'].includes(process.argv[2]))
  throw new Error('Use --write or --check')
if (process.argv[2] === '--write') writeFileSync(fixturePath, output)
else if (readFileSync(fixturePath, 'utf8') !== output)
  throw new Error('Small-circuit fixture differs from the pinned independent oracle')
console.log('PASS: independent one-public-input Groth16 setup/proof, changed-signal rejection and schoolbook H fixture')
