import { readFileSync, writeFileSync } from 'node:fs'
import { gunzipSync } from 'node:zlib'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { performance } from 'node:perf_hooks'
import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'

// Development oracle only: exact pinned SDK formula on a public test witness.
// The runnable Tornado CLI and its proof path remain entirely native Lean.
const lean = fileURLToPath(new URL('../', import.meta.url))
const source = resolve(lean, '../tornado-cli-new-era')
const sourceCommit = 'daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7'
if (execFileSync('git', ['-C', source, 'rev-parse', 'HEAD'],
  { encoding: 'utf8' }).trim() !== sourceCommit)
  throw new Error('The pinned TypeScript CLI checkout moved')
const version = file => JSON.parse(readFileSync(resolve(source, file), 'utf8')).version
if (version('node_modules/@kohaku-eth/tornado-cash/package.json') !== '0.1.0-alpha.38' ||
    version('node_modules/micro-zk-proofs/package.json') !== '0.3.1' ||
    version('node_modules/micro-zk-proofs/node_modules/@noble/curves/package.json') !== '2.2.0')
  throw new Error('The pinned Groth16 or noble oracle version changed')
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex')
const { buildSnark } = await import(pathToFileURL(resolve(source,
  'node_modules/micro-zk-proofs/index.js')).href)
const { bn254 } = await import(pathToFileURL(resolve(source,
  'node_modules/micro-zk-proofs/node_modules/@noble/curves/bn254.js')).href)
const Fp = bn254.fields.Fp
const Fr = bn254.fields.Fr
const key = gunzipSync(readFileSync(resolve(lean,
  'assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz')))
const keySHA256 = sha256(key)
if (keySHA256 !== '8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af')
  throw new Error('Pinned proving-key bytes changed')
const dv = new DataView(key.buffer, key.byteOffset, key.byteLength)
const u32 = offset => dv.getUint32(offset, true)
const [nVars, nPublic, domainSize, polsA, polsB, pointsA, pointsB1,
  pointsB2, pointsC, hExps] = Array.from({ length: 10 }, (_, i) => u32(i * 4))
if (nVars !== 28300 || nPublic !== 6 || domainSize !== 32768)
  throw new Error('Unexpected proving-key dimensions')
const R = 2n ** 256n
const invFp = Fp.inv(R % Fp.ORDER)
const invFr = Fr.inv(R % Fr.ORDER)
const le32 = offset => {
  let value = 0n
  for (let i = 31; i >= 0; i--) value = value * 256n + BigInt(key[offset + i])
  return value
}
const montFp = offset => Fp.mul(le32(offset), invFp)
const montFr = offset => Fr.mul(le32(offset), invFr)
const g1 = offset => {
  const x = montFp(offset)
  const y = montFp(offset + 32)
  return x === 0n && y === 1n ? null : [x, y, 1n]
}
const g2 = offset => {
  const x0 = montFp(offset)
  const x1 = montFp(offset + 32)
  const y0 = montFp(offset + 64)
  const y1 = montFp(offset + 96)
  return x0 === 0n && x1 === 0n && y0 === 1n && y1 === 0n
    ? null : [[x0, x1], [y0, y1], [1n, 0n]]
}
const readPoints = (offset, count, stride, read) =>
  Array.from({ length: count }, (_, i) => read(offset + i * stride))
function polynomials(offset) {
  const pols = []
  for (let signal = 0; signal < nVars; signal++) {
    const entries = {}
    const count = u32(offset)
    offset += 4
    for (let i = 0; i < count; i++) {
      const row = u32(offset)
      offset += 4
      const coefficient = montFr(offset)
      offset += 32
      if (coefficient !== 0n) entries[row] = coefficient
    }
    pols.push(entries)
  }
  return pols
}
const started = performance.now()
const provingKey = {
  nVars, nPublic, domainBits: Math.log2(domainSize), domainSize,
  polsA: polynomials(polsA), polsB: polynomials(polsB),
  polsC: Array.from({ length: nVars }, () => ({})),
  A: readPoints(pointsA, nVars, 64, g1),
  B1: readPoints(pointsB1, nVars, 64, g1),
  B2: readPoints(pointsB2, nVars, 128, g2),
  C: new Array(nPublic + 1).fill(null)
    .concat(readPoints(pointsC, nVars - nPublic - 1, 64, g1)),
  hExps: readPoints(hExps, domainSize - 1, 64, g1),
  vk_alfa_1: g1(40), vk_beta_1: g1(104), vk_delta_1: g1(168),
  vk_beta_2: g2(232), vk_delta_2: g2(360),
}
const witnessFixture = readFileSync(resolve(lean,
  'fixtures/groth16-tornado-r1cs.json'))
const witnessFixtureSHA256 = sha256(witnessFixture)
if (witnessFixtureSHA256 !== '10364ef4ca2a0436435ee40d2cd1376b2dd1c5d79278e8addabcbae38b56920c')
  throw new Error('Pinned public witness fixture changed')
const witness = JSON.parse(witnessFixture.toString('utf8')).witness.map(BigInt)
if (witness.length !== nVars || witness[0] !== 1n)
  throw new Error('Unexpected public witness')
const relayerProfile = ['--relayer-write', '--relayer-check'].includes(process.argv[2])
if (relayerProfile) {
  // Public, unfunded fixture only. The circuit binds these two public
  // inputs through their dummy square constraints in the final witness slots.
  witness[4] = 187n
  witness[5] = 860000000000000n
  witness[28298] = Fr.sqr(witness[4])
  witness[28297] = Fr.sqr(witness[5])
}
const constraints = JSON.parse(witnessFixture.toString('utf8')).constraints
const linear = side => Object.entries(side).reduce((sum, [slot, coefficient]) =>
  Fr.add(sum, Fr.mul(BigInt(coefficient), witness[Number(slot)])), 0n)
if (constraints.length !== 28275 || constraints.some(([a, b, c]) =>
  Fr.mul(linear(a), linear(b)) !== linear(c)))
  throw new Error('The public proof witness does not satisfy every pinned R1CS constraint')
const keyParseMs = Math.round(performance.now() - started)
const snark = buildSnark(bn254, { nqr: 7 })
let calls = 0
const rnd = size => {
  if (size !== 32 || calls > 1) throw new Error('Unexpected blinding request')
  const bytes = new Uint8Array(size)
  bytes[size - 1] = ++calls
  return bytes
}
const proof = await snark.groth.createProof(provingKey, witness, rnd)
if (calls !== 2) throw new Error('Blinding requests changed')
const p = proof.proof
const limbs = [p.pi_a[0], p.pi_a[1], p.pi_b[0][1], p.pi_b[0][0],
  p.pi_b[1][1], p.pi_b[1][0], p.pi_c[0], p.pi_c[1]]
const hex = '0x' + limbs.map(value => BigInt(value).toString(16).padStart(64, '0')).join('')
const output = JSON.stringify({
  sourceCommit,
  sdk: '@kohaku-eth/tornado-cash@0.1.0-alpha.38',
  prover: 'micro-zk-proofs@0.3.1 with NQR 7 and noble BN254',
  provingKeySHA256: keySHA256,
  publicWitnessFixtureSHA256: witnessFixtureSHA256,
  ...(relayerProfile ? { profile: 'unfunded Classic relayer; reward=187; fee=860000000000000' } : {}),
  blindingR: '1', blindingS: '2',
  publicSignals: proof.publicSignals.map(String),
  solidityProofHex: hex,
  solidityProofSHA256: sha256(Buffer.from(hex.slice(2), 'hex')),
}, null, 2) + '\n'
const fixturePath = resolve(lean, relayerProfile
  ? 'fixtures/groth16-relayer-public-proof.json' : 'fixtures/groth16-full-public-proof.json')
if (process.argv[2] === '--write' || process.argv[2] === '--relayer-write') {
  writeFileSync(fixturePath, output)
  console.log(`Wrote pinned public full proof vector (oracle key parse ${keyParseMs} ms)`)
} else if (process.argv[2] === '--check' || process.argv[2] === '--relayer-check') {
  if (readFileSync(fixturePath, 'utf8') !== output)
    throw new Error('Full public proof differs from the pinned JS oracle')
  console.log(relayerProfile
    ? 'PASS: public Classic relayer proof bytes match pinned micro-zk-proofs and all R1CS constraints'
    : 'PASS: full public Groth16 proof bytes match pinned micro-zk-proofs')
} else {
  throw new Error('Use --write, --check, --relayer-write or --relayer-check')
}
