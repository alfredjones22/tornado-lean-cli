#!/usr/bin/env node
// Development-only vectors from the exact pinned noble BN254 Fr FFT.
import { createRequire } from 'node:module'
import { readFileSync, writeFileSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { pathToFileURL, fileURLToPath } from 'node:url'
import { assertOracleIdentity } from './oracle-identity.mjs'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
const source = resolve(process.env.TORNADO_TS_CLI || join(root, '..', 'tornado-cli-new-era'))
const fixturePath = resolve(process.env.FR_FFT_FIXTURE_PATH || join(root, 'fixtures/fr-fft-vectors.json'))
assertOracleIdentity(source)
const sourcePackage = JSON.parse(readFileSync(join(source, 'package.json'), 'utf8'))
if (sourcePackage.dependencies['micro-zk-proofs'] !== '0.3.1' ||
    sourcePackage.dependencies['@kohaku-eth/tornado-cash'] !== '0.1.0-alpha.40')
  throw new Error('The pinned TypeScript FFT dependencies changed')
const requireFromSource = createRequire(join(source, 'package.json'))
const { bn254 } = await import(pathToFileURL(requireFromSource.resolve('@noble/curves/bn254.js')))
const { FFT, poly, rootsOfUnity } = await import(
  pathToFileURL(requireFromSource.resolve('@noble/curves/abstract/fft.js')))
const Fr = bn254.fields.Fr
const roots = rootsOfUnity(Fr, 7n)
const fft = FFT(roots, Fr)
const polynomial = poly(Fr, roots, undefined, fft)
if (roots.info.G !== 7n || roots.info.powerOfTwo !== 28)
  throw new Error('NQR 7 did not produce the expected BN254 Fr root tower')

const str = values => values.map(value => value.toString())
const inputFor = n => Array.from({ length: n }, (_, i) =>
  i % 7 === 0 ? Fr.ORDER - BigInt(i + 1) :
    BigInt((i + 1) * (i * i + 7)))

const fftCases = [1, 2, 4, 8, 16, 32, 64].map(n => {
  const input = inputFor(n)
  const transformed = fft.direct(input)
  const restored = fft.inverse(transformed)
  if (restored.some((value, i) => value !== input[i]))
    throw new Error(`Noble FFT roundtrip failed at n=${n}`)
  return { n, input: str(input), transformed: str(transformed) }
})

const largeInput = new Array(32768).fill(0n)
const largeNonzero = [
  { index: 0, value: 1n },
  { index: 1, value: 42n },
  { index: 127, value: Fr.ORDER - 7n },
  { index: 32767, value: 123456789n },
]
for (const row of largeNonzero) largeInput[row.index] = row.value
const largeTransformed = fft.direct(largeInput)
const largeSampleIndices = [0, 1, 2, 3, 17, 1024, 16384, 32767]
const largeCase = { n: largeInput.length,
  nonzero: largeNonzero.map(row => ({ index: row.index, value: row.value.toString() })),
  samples: largeSampleIndices.map(index => ({ index,
    value: largeTransformed[index].toString() })),
}

const hCases = [4, 8, 16].map(domainSize => {
  const witness = [1n, 5n, 9n]
  const makePols = matrix => witness.map((_, signal) => ({
    entries: Array.from({ length: domainSize }, (_, i) => {
      const raw = (matrix + signal * 3 + i * i + i * 5) % 13
      if (raw % 4 === 0) return undefined
      return { constraint: i, coefficient: BigInt(raw + 1) }
    }).filter(Boolean),
  }))
  const polsA = makePols(2)
  const polsB = makePols(7)
  const sum = pols => {
    const result = new Array(domainSize).fill(0n)
    for (let s = 0; s < witness.length; s++)
      for (const entry of pols[s].entries)
        result[entry.constraint] = Fr.add(result[entry.constraint],
          Fr.mul(witness[s], entry.coefficient))
    return result
  }
  const pA = sum(polsA)
  const pB = sum(polsB)
  const a = fft.inverse(pA)
  const b = fft.inverse(pB)
  const product = polynomial.convolve(a, b)
  while (product.length && product.at(-1) === 0n) product.pop()
  const h = product.slice(domainSize)
  // The upper half must also equal the naive coefficient convolution.
  const naive = new Array(2 * domainSize - 1).fill(0n)
  for (let i = 0; i < domainSize; i++)
    for (let j = 0; j < domainSize; j++)
      naive[i + j] = Fr.add(naive[i + j], Fr.mul(a[i], b[j]))
  while (naive.length && naive.at(-1) === 0n) naive.pop()
  if (h.some((value, i) => value !== naive[domainSize + i]))
    throw new Error(`Noble H differs from naive convolution at n=${domainSize}`)
  return { domainSize, witness: str(witness),
    polsA: polsA.map(pol => ({ entries: pol.entries.map(entry => ({
      constraint: entry.constraint, coefficient: entry.coefficient.toString(),
    })) })),
    polsB: polsB.map(pol => ({ entries: pol.entries.map(entry => ({
      constraint: entry.constraint, coefficient: entry.coefficient.toString(),
    })) })),
    pA: str(pA), pB: str(pB), h: str(h) }
})

const output = JSON.stringify({
  source: 'tornado-cli-new-era micro-zk-proofs@0.3.1 noble-curves BN254 Fr',
  nqr: '7', modulus: Fr.ORDER.toString(),
  omega32768: roots.omega(15).toString(),
  omega65536: roots.omega(16).toString(),
  inverse32768: Fr.inv(32768n).toString(),
  fftCases, largeCase, hCases,
}, null, 2) + '\n'

if (process.argv[2] === '--write') {
  writeFileSync(fixturePath, output)
  console.log(`Wrote ${fftCases.length} FFT and ${hCases.length} H vectors`)
} else if (process.argv[2] === '--check') {
  if (readFileSync(fixturePath, 'utf8') !== output)
    throw new Error('Pinned Fr FFT fixture changed')
  console.log(`PASS: ${fftCases.length} FFT and ${hCases.length} H vectors match pinned noble BN254 Fr`)
} else {
  throw new Error('Use --write or --check')
}
