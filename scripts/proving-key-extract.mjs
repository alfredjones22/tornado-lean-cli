#!/usr/bin/env node
// Development-only public vectors from the exact pinned Tornado proving key.
// Runtime parsing and arithmetic are implemented independently in Lean.
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync } from 'node:fs'
import { gunzipSync } from 'node:zlib'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
const keyPath = join(root, 'assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz')
const fixturePath = join(root, 'fixtures/proving-key-vectors.json')
const pinnedSHA256 = '8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af'
const fp = BigInt('0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47')
const fr = BigInt('0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001')

function requireThat(condition, message) {
  if (!condition) throw new Error(message)
}

function modPow(base, exponent, modulus) {
  let result = 1n
  while (exponent > 0n) {
    if (exponent & 1n) result = result * base % modulus
    base = base * base % modulus
    exponent >>= 1n
  }
  return result
}

function uintLE(bytes) {
  let value = 0n
  for (let i = bytes.length - 1; i >= 0; i--) value = value * 256n + BigInt(bytes[i])
  return value
}

const raw = gunzipSync(readFileSync(keyPath))
const sha256 = createHash('sha256').update(raw).digest('hex')
requireThat(sha256 === pinnedSHA256 && raw.length === 14522256,
  'Pinned proving key digest or length changed')
const dv = new DataView(raw.buffer, raw.byteOffset, raw.byteLength)
const u32 = (offset) => dv.getUint32(offset, true)
const nVars = u32(0)
const nPublic = u32(4)
const domainSize = u32(8)
const polsA = u32(12)
const polsB = u32(16)
const pointsA = u32(20)
const pointsB1 = u32(24)
const pointsB2 = u32(28)
const pointsC = u32(32)
const hExps = u32(36)
requireThat(nVars === 28300 && nPublic === 6 && domainSize === 32768 &&
  polsA === 488 && polsB === 1506204 && pointsA === 3369616 &&
  pointsB1 === 5180816 && pointsB2 === 6992016 &&
  pointsC === 10614416 && hExps === 12425168,
'Pinned proving key header changed')

const fpRInv = modPow(2n ** 256n % fp, fp - 2n, fp)
const frRInv = modPow(2n ** 256n % fr, fr - 2n, fr)
requireThat((2n ** 256n * fpRInv) % fp === 1n &&
  (2n ** 256n * frRInv) % fr === 1n, 'Montgomery inverses are invalid')
const fromMont = (bytes, prime, inverse) => {
  const encoded = uintLE(bytes)
  requireThat(encoded < prime, 'Noncanonical Montgomery field element in key')
  return encoded * inverse % prime
}

const pointOffsets = [
  ['vk_alpha', 40], ['vk_beta', 104], ['vk_delta', 168],
  ['A_0', pointsA], ['A_7', pointsA + 7 * 64],
  ['A_last', pointsA + (nVars - 1) * 64],
  ['B1_0', pointsB1], ['B1_last', pointsB1 + (nVars - 1) * 64],
  ['C_0', pointsC], ['C_last', pointsC + (nVars - nPublic - 2) * 64],
  ['H_0', hExps], ['H_last', hExps + (domainSize - 2) * 64],
]
const pointSamples = pointOffsets.map(([name, offset]) => {
  const bytes = raw.subarray(offset, offset + 64)
  const x = fromMont(bytes.subarray(0, 32), fp, fpRInv)
  const y = fromMont(bytes.subarray(32, 64), fp, fpRInv)
  const identity = x === 0n && y === 1n
  requireThat(identity || y * y % fp === (x * x % fp * x + 3n) % fp,
    `G1 key point ${name} is not on the curve`)
  return { name, offset, rawHex: bytes.toString('hex'),
    identity, x: x.toString(), y: y.toString() }
})

// These four affine coordinates use the SDK's Fp2 `(c0,c1)` order. Solidity
// proof serialization later swaps that order; the key parser does not.
const g2Offsets = [
  ['vk_beta_2', 232], ['vk_delta_2', 360],
  ['B2_0', pointsB2], ['B2_7', pointsB2 + 7 * 128],
  ['B2_last', pointsB2 + (nVars - 1) * 128],
]
const fp2Add = ([a, b], [c, d]) => [(a + c) % fp, (b + d) % fp]
const fp2Mul = ([a, b], [c, d]) => [
  (a * c - b * d + fp * fp) % fp,
  (a * d + b * c) % fp,
]
const g2TwistB = [
  19485874751759354771024239261021720505790618469301721065564631296452457478373n,
  266929791119991161246907387137283842545076965332900288569378510910307636690n,
]
const g2Samples = g2Offsets.map(([name, offset]) => {
  const bytes = raw.subarray(offset, offset + 128)
  const fields = Array.from({ length: 4 }, (_, i) =>
    fromMont(bytes.subarray(i * 32, (i + 1) * 32), fp, fpRInv))
  const x = [fields[0], fields[1]]
  const y = [fields[2], fields[3]]
  const identity = x[0] === 0n && x[1] === 0n && y[0] === 1n && y[1] === 0n
  const left = fp2Mul(y, y)
  const right = fp2Add(fp2Mul(fp2Mul(x, x), x), g2TwistB)
  requireThat(identity || left.every((value, i) => value === right[i]),
    `G2 key point ${name} is not on the twist`)
  return { name, offset, rawHex: bytes.toString('hex'), identity,
    x0: x[0].toString(), x1: x[1].toString(),
    y0: y[0].toString(), y1: y[1].toString() }
})

// Signal zero has tens of thousands of coefficients and would make this
// small reproducible vector fixture several megabytes on its own.
const selectedSignals = new Set([1, 7, 14150, nVars - 1])
const polynomialSamples = []
for (const [section, start, stop] of [
  ['A', polsA, polsB], ['B', polsB, pointsA]]) {
  let offset = start
  for (let signal = 0; signal < nVars; signal++) {
    const begin = offset
    const count = u32(offset)
    offset += 4
    requireThat(count <= domainSize && offset + count * 36 <= stop,
      `Malformed ${section} polynomial ${signal}`)
    const entries = []
    const seen = new Set()
    for (let i = 0; i < count; i++) {
      const constraint = u32(offset)
      const coefficient = fromMont(raw.subarray(offset + 4, offset + 36), fr, frRInv)
      requireThat(constraint < domainSize && !seen.has(constraint),
        `Duplicate or out-of-range ${section} polynomial row ${constraint}`)
      seen.add(constraint)
      entries.push({ constraint, coefficient: coefficient.toString() })
      offset += 36
    }
    if (selectedSignals.has(signal)) polynomialSamples.push({
      section, signal, offset: begin, nextOffset: offset,
      rawHex: raw.subarray(begin, offset).toString('hex'), entries,
    })
  }
  requireThat(offset === stop, `Polynomial section ${section} did not end at the pinned offset`)
}

const output = JSON.stringify({
  sourceKeySha256: sha256,
  fpRInv: fpRInv.toString(),
  frRInv: frRInv.toString(),
  pointSamples,
  g2Samples,
  polynomialSamples,
}, null, 2) + '\n'

if (process.argv[2] === '--write') {
  writeFileSync(fixturePath, output)
  console.log(`Wrote ${pointSamples.length} G1, ${g2Samples.length} G2, and ${polynomialSamples.length} polynomial vectors`)
} else if (process.argv[2] === '--check') {
  requireThat(readFileSync(fixturePath, 'utf8') === output,
    'Proving-key vectors differ from the pinned binary asset')
  console.log(`PASS: ${pointSamples.length} G1, ${g2Samples.length} G2, and ${polynomialSamples.length} polynomial vectors match the pinned key`)
} else {
  throw new Error('Use --write or --check')
}
