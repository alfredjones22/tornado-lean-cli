#!/usr/bin/env node
// Development-only extractor for the selected Circom component graph. The
// runtime witness evaluator is native Lean and never invokes this script.
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync } from 'node:fs'
import { gunzipSync } from 'node:zlib'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const here = dirname(fileURLToPath(import.meta.url))
const root = join(here, '..')
const asset = join(root, 'assets/proving/tornado-3ddd61dbff09caee.json.gz')
const destination = join(root, 'fixtures/witness-vm-selected-components.json')
const pinnedCircuitSHA256 = '3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98'

function requireThat(condition, description) {
  if (!condition) throw new Error(description)
}

const raw = gunzipSync(readFileSync(asset))
const actualSHA256 = createHash('sha256').update(raw).digest('hex')
requireThat(actualSHA256 === pinnedCircuitSHA256, 'Circuit asset differs from the pinned source')
const circuit = JSON.parse(raw.toString('utf8'))
requireThat(circuit.nVars === 28300 && circuit.nSignals === 36528,
  'Pinned circuit signal dimensions changed')

// Canonicalize the decoded R1CS, so the Lean checked-witness API can bind
// its caller-supplied Circuit structure to the exact pinned constraints.
// Numeric sorting removes JSON object-key ordering from the commitment.
const canonicalRow = (row) => Object.entries(row)
  .sort(([left], [right]) => Number(left) - Number(right))
  .map(([index, coefficient]) => `${index}:${coefficient}`)
  .join(',')
const canonicalCircuit = `${circuit.nVars}/${circuit.nPubInputs + circuit.nOutputs}/${circuit.constraints.length}\n` +
  circuit.constraints.map(([a, b, c]) =>
    `${canonicalRow(a)}|${canonicalRow(b)}|${canonicalRow(c)}`).join('\n')
const r1csCanonicalSHA256 = createHash('sha256').update(canonicalCircuit).digest('hex')
requireThat(r1csCanonicalSHA256 === '8e009dc9070dbaa70a9b803e3ec31f18b47b7ec437ba39535dd003f7d848036b',
  `Pinned canonical R1CS digest changed: ${r1csCanonicalSHA256}`)

function idx(name) {
  const value = circuit.signalName2Idx[name]
  requireThat(Number.isSafeInteger(value) && value >= 0 && value < circuit.nSignals,
    `Missing signal ${name}`)
  return value
}

const bitNames = ['main.hasher.nullifierBits', 'main.hasher.secretBits']
const num2bits = bitNames.map((name) => {
  const component = circuit.components.find((item) => item.name === name)
  requireThat(component?.template === 'Num2Bits' && component.params.n === '248',
    `Unexpected ${name} component`)
  return {
    name,
    input: idx(`${name}.in`),
    outputs: Array.from({ length: 248 }, (_, bit) => idx(`${name}.out[${bit}]`)),
  }
})

const merkle = Array.from({ length: 20 }, (_, level) => {
  const selectorName = `main.tree.selectors[${level}]`
  const hasherName = `main.tree.hashers[${level}]`
  requireThat(circuit.components.some((item) =>
    item.name === selectorName && item.template === 'DualMux'),
  `Unexpected ${selectorName} component`)
  requireThat(circuit.components.some((item) =>
    item.name === hasherName && item.template === 'HashLeftRight'),
  `Unexpected ${hasherName} component`)
  const row = {
    level,
    leftInput: idx(`${selectorName}.in[0]`),
    rightInput: idx(`${selectorName}.in[1]`),
    selector: idx(`${selectorName}.s`),
    leftOutput: idx(`${selectorName}.out[0]`),
    rightOutput: idx(`${selectorName}.out[1]`),
    hashOutput: idx(`${hasherName}.hash`),
  }
  requireThat(idx(`${hasherName}.left`) === row.leftOutput &&
    idx(`${hasherName}.right`) === row.rightOutput,
  `Hasher ${level} is not driven by the selector`)
  requireThat(row.rightInput === 9 + level && row.selector === 29 + level &&
    row.leftInput === (level === 0 ? 49 :
      idx(`main.tree.hashers[${level - 1}].hash`)),
  `Merkle level ${level} wiring differs from the witness input prefix`)
  return row
})

const feistel = Array.from({ length: 20 }, (_, level) => {
  const hasherName = `main.tree.hashers[${level}].hasher`
  requireThat(circuit.components.some((item) =>
    item.name === hasherName && item.template === 'MiMCSponge' &&
    item.params.nInputs === '2' && item.params.nOutputs === '1'),
  `Unexpected ${hasherName} sponge`)
  requireThat(idx(`${hasherName}.ins[0]`) === merkle[level].leftOutput &&
    idx(`${hasherName}.ins[1]`) === merkle[level].rightOutput &&
    idx(`${hasherName}.outs[0]`) === merkle[level].hashOutput,
  `MiMC sponge ${level} is not wired to the Merkle stage`)
  const stages = Array.from({ length: 2 }, (_, stage) => {
    const name = `${hasherName}.S[${stage}]`
    requireThat(circuit.components.some((item) =>
      item.name === name && item.template === 'MiMCFeistel' &&
      item.params.nrounds === '220'),
    `Unexpected ${name} permutation`)
    return {
      key: idx(`${name}.k`),
      leftInput: idx(`${name}.xL_in`),
      rightInput: idx(`${name}.xR_in`),
      leftOutput: idx(`${name}.xL_out`),
      rightOutput: idx(`${name}.xR_out`),
      t2: Array.from({ length: 220 }, (_, round) => idx(`${name}.t2[${round}]`)),
      t4: Array.from({ length: 220 }, (_, round) => idx(`${name}.t4[${round}]`)),
      leftRounds: Array.from({ length: 219 }, (_, round) => idx(`${name}.xL[${round}]`)),
      rightRounds: Array.from({ length: 219 }, (_, round) => idx(`${name}.xR[${round}]`)),
    }
  })
  requireThat(stages[0].leftInput === merkle[level].leftOutput &&
    stages[1].rightInput === stages[0].rightOutput &&
    stages[1].leftOutput === merkle[level].hashOutput &&
    stages[0].key === idx(`${hasherName}.k`) &&
    stages[1].key === idx(`${hasherName}.k`),
  `MiMC Feistel ${level} internal wiring differs from the pinned program`)
  return stages
})

// The Pedersen template sets BabyJubJub base points as constants, then wires
// every arithmetic component through shared signal identifiers. The extractor selects a
// small typed arithmetic program instead of embedding or executing JavaScript
// in the Lean runtime.
const baseMatch = circuit.templates.Pedersen.match(
  /ctx\.setVar\("BASE", \[\], (\[\[[\s\S]*?\]\])\);/)
requireThat(baseMatch !== null, 'Pinned Pedersen base-point table is missing')
const basePoints = JSON.parse(baseMatch[1])
requireThat(basePoints.length === 10 && basePoints.every((point) =>
  point.length === 2 && point.every((value) => /^\d+$/.test(value))),
'Pinned Pedersen base-point table has an unexpected shape')
const bases = []
for (const pedersen of circuit.components.filter((item) => item.template === 'Pedersen')) {
  const bitLength = Number(pedersen.params.n)
  requireThat(bitLength === 496 || bitLength === 248,
    `Unexpected Pedersen bit length in ${pedersen.name}`)
  const segments = Math.ceil(bitLength / 200)
  for (let i = 0; i < segments; i++) {
    for (let coordinate = 0; coordinate < 2; coordinate++) {
      bases.push({
        index: idx(`${pedersen.name}.segments[${i}].base[${coordinate}]`),
        value: basePoints[i][coordinate],
      })
    }
  }
}
requireThat(bases.length === 10, 'Expected five instantiated Pedersen segments')

function primitive(component) {
  const at = (name) => idx(`${component.name}.${name}`)
  let inputs
  let outputs
  switch (component.template) {
    case 'MontgomeryAdd':
      inputs = ['in1[0]', 'in1[1]', 'in2[0]', 'in2[1]']
      outputs = ['lamda', 'out[0]', 'out[1]']
      break
    case 'MontgomeryDouble':
      inputs = ['in[0]', 'in[1]']
      outputs = ['x1_2', 'lamda', 'out[0]', 'out[1]']
      break
    case 'Edwards2Montgomery':
    case 'Montgomery2Edwards':
      inputs = ['in[0]', 'in[1]']
      outputs = ['out[0]', 'out[1]']
      break
    case 'BabyAdd':
      inputs = ['x1', 'y1', 'x2', 'y2']
      outputs = ['beta', 'gamma', 'delta', 'tau', 'xout', 'yout']
      break
    case 'Window4':
      requireThat(at('out[0]') === at('mux.out[0]'),
        `Window4 x output is not aliased to its mux in ${component.name}`)
      inputs = ['mux.out[1]', 'in[3]']
      outputs = ['out[1]']
      break
    case 'MultiMux3':
      requireThat(component.params.n === '2',
        `Unexpected MultiMux3 width in ${component.name}`)
      inputs = ['s[0]', 's[1]', 's[2]',
        ...Array.from({ length: 2 }, (_, coordinate) =>
          Array.from({ length: 8 }, (_, digit) => `c[${coordinate}][${digit}]`)).flat()]
      outputs = ['s10',
        ...['a210', 'a21', 'a20', 'a2', 'a10', 'a1', 'a0', 'a', 'out']
          .flatMap((name) => [`${name}[0]`, `${name}[1]`])]
      break
    default:
      return null
  }
  return {
    kind: component.template,
    name: component.name,
    inputs: inputs.map(at),
    outputs: outputs.map(at),
  }
}

const unsorted = circuit.components.map(primitive).filter(Boolean)
for (const [name, input] of [
  ['recipientSquare', 'recipient'], ['feeSquare', 'fee'],
  ['relayerSquare', 'relayer'], ['refundSquare', 'refund']]) {
  unsorted.push({ kind: 'Square', name: `main.${name}`,
    inputs: [idx(`main.${input}`)], outputs: [idx(`main.${name}`)] })
}

const known = new Set([
  ...Array.from({ length: 50 }, (_, i) => i),
  ...num2bits.flatMap((component) => component.outputs),
  ...bases.map((seed) => seed.index),
])
const primitives = []
let pending = unsorted
while (pending.length) {
  const next = []
  let progressed = false
  for (const operation of pending) {
    if (operation.inputs.every((input) => known.has(input))) {
      primitives.push(operation)
      for (const output of operation.outputs) known.add(output)
      progressed = true
    } else next.push(operation)
  }
  requireThat(progressed,
    `Pedersen primitive graph is incomplete: ${next.slice(0, 3).map((item) =>
      `${item.name} missing ${item.inputs.filter((index) => !known.has(index)).join(',')}`).join('; ')}`)
  pending = next
}
requireThat(primitives.length === unsorted.length,
  'A Pedersen primitive was omitted from the topological program')

requireThat(num2bits[0].input === 7 && num2bits[1].input === 8,
  'Bit decomposition inputs differ from native note prefix')
requireThat(idx('main.hasher.commitment') === 49 && idx('main.root') === 1,
  'Commitment or root signal differs from expected witness slots')
const output = JSON.stringify({
  schemaVersion: 1,
  sourceCircuitSha256: actualSHA256,
  nSignals: circuit.nSignals,
  nVars: circuit.nVars,
  commitmentSignal: 49,
  rootSignal: 1,
  num2bits,
  merkle,
  feistel,
  bases,
  primitives,
}, null, 2) + '\n'

if (process.argv[2] === '--write') {
  writeFileSync(destination, output)
  console.log('Wrote selected component graph from pinned circuit')
} else if (process.argv[2] === '--check') {
  requireThat(readFileSync(destination, 'utf8') === output,
    'Selected component graph does not match the pinned circuit')
  console.log('PASS: selected component graph equals pinned circuit metadata')
} else {
  throw new Error('Use --write or --check')
}
