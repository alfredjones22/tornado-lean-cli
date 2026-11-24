#!/usr/bin/env node
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { gunzipSync } from 'node:zlib'

// Exhaustive comparison of public artifact coefficients, not a sampled
// witness test or a Lean theorem about the binary parser/setup ceremony.
const root = fileURLToPath(new URL('../', import.meta.url))
const check = (value, message) => { if (!value) throw new Error(message) }
const hash = value => createHash('sha256').update(value).digest('hex')
const circuitRaw = gunzipSync(readFileSync(`${root}assets/proving/tornado-3ddd61dbff09caee.json.gz`))
const key = gunzipSync(readFileSync(`${root}assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz`))
check(circuitRaw.length === 19474889 &&
  hash(circuitRaw) === '3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98' &&
  key.length === 14522256 &&
  hash(key) === '8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af',
'QAP input artifact identity differs')
const circuit = JSON.parse(circuitRaw.toString('utf8'))
const q = 21888242871839275222246405745257275088548364400416034343698204186575808495617n
const power = (base, exponent) => {
  let result = 1n
  while (exponent > 0n) {
    if (exponent % 2n) result = result * base % q
    base = base * base % q
    exponent /= 2n
  }
  return result
}
const inverse = power(2n ** 256n % q, q - 2n)
check(2n ** 256n * inverse % q === 1n, 'Invalid Montgomery inverse')
const u32 = offset => key.readUInt32LE(offset)
const nVars = u32(0), nPublic = u32(4), domain = u32(8)
check(nVars === 28300 && nPublic === 6 && domain === 32768 &&
  circuit.nVars === nVars && circuit.nPubInputs + circuit.nOutputs === nPublic &&
  circuit.constraints.length === 28275 && domain >= circuit.constraints.length + nPublic + 1,
'QAP dimensions differ')
const counts = []
for (const [side, start, stop] of [[0, u32(12), u32(16)], [1, u32(16), u32(20)]]) {
  const expected = new Map()
  for (let row = 0; row < circuit.constraints.length; row++) {
    for (const [rawSignal, rawCoefficient] of Object.entries(circuit.constraints[row][side])) {
      const signal = Number(rawSignal), coefficient = BigInt(rawCoefficient)
      check(Number.isSafeInteger(signal) && signal >= 0 && signal < nVars &&
        String(signal) === rawSignal && coefficient >= 0n && coefficient < q,
      'Invalid circuit row coefficient')
      if (coefficient !== 0n) expected.set(`${row}:${signal}`, coefficient)
    }
  }
  // Legacy Groth16 binds the constant/public slots with A-only rows after
  // the actual circuit constraints. All other padded rows are zero.
  if (side === 0) for (let signal = 0; signal <= nPublic; signal++)
    expected.set(`${circuit.constraints.length + signal}:${signal}`, 1n)
  let offset = start, count = 0
  for (let signal = 0; signal < nVars; signal++) {
    check(offset + 4 <= stop, 'Truncated polynomial header')
    const length = u32(offset); offset += 4
    check(length <= domain && offset + length * 36 <= stop, 'Invalid polynomial row count')
    const seen = new Set()
    for (let entry = 0; entry < length; entry++) {
      const row = u32(offset)
      let encoded = 0n
      for (let byte = 31; byte >= 0; byte--) encoded = encoded * 256n + BigInt(key[offset + 4 + byte])
      check(row < domain && !seen.has(row) && encoded < q, 'Invalid or duplicate polynomial entry')
      seen.add(row)
      const coefficient = encoded * inverse % q, name = `${row}:${signal}`
      check(coefficient !== 0n && expected.get(name) === coefficient,
        `QAP ${'AB'[side]} differs at row ${row}, signal ${signal}`)
      expected.delete(name)
      offset += 36; count++
    }
  }
  check(offset === stop && expected.size === 0, `QAP ${'AB'[side]} section is incomplete`)
  counts.push(count)
}
check(counts[0] === 38681 && counts[1] === 48617, 'QAP coefficient inventory changed')
console.log('PASS: all 38681 A and 48617 B key coefficients match the complete circuit, seven public-slot augmentation rows and zero padding')
