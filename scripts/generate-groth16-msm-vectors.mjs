import { readFileSync, writeFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

// Public synthetic query points and scalars. Runtime MSM/proof assembly is Lean.
const root = fileURLToPath(new URL('../', import.meta.url))
const source = resolve(root, '../tornado-cli-new-era')
const { bn254 } = await import(pathToFileURL(resolve(source,
  'node_modules/@noble/curves/bn254.js')).href)
const order = bn254.fields.Fr.ORDER
const G1 = bn254.G1.Point
const G2 = bn254.G2.Point

const point1 = scalar => G1.BASE.multiplyUnsafe(BigInt(scalar))
const point2 = scalar => G2.BASE.multiplyUnsafe(BigInt(scalar))
const encode1 = point => point.equals(G1.ZERO) ? null :
  Object.fromEntries(Object.entries(point.toAffine()).map(([key, value]) => [key, value.toString()]))
const encode2 = point => {
  if (point.equals(G2.ZERO)) return null
  const { x, y } = point.toAffine()
  return { x0: x.c0.toString(), x1: x.c1.toString(),
    y0: y.c0.toString(), y1: y.c1.toString() }
}
const msm = (Point, points, scalars) => {
  if (points.length !== scalars.length) throw new Error('MSM vector count mismatch')
  return points.reduce((sum, point, i) => sum.add(point.multiplyUnsafe(BigInt(scalars[i]))), Point.ZERO)
}
const key = {
  nPublic: 1,
  vkAlpha1: point1(23), vkBeta1: point1(29), vkDelta1: point1(31),
  vkBeta2: point2(37), vkDelta2: point2(41),
  queryA: [point1(1), point1(2), G1.ZERO, point1(4)],
  queryB1: [point1(5), G1.ZERO, point1(3), point1(7)],
  queryB2: [point2(2), point2(3), G2.ZERO, point2(5)],
  queryC: [point1(11), point1(13)],
  hExps: [point1(17), point1(19)],
}
const witness = [1n, 2n, 3n, 4n]
const h = [6n, 7n]
const r = 43n
const s = 47n
const piA = msm(G1, key.queryA, witness).add(key.vkAlpha1)
  .add(key.vkDelta1.multiplyUnsafe(r))
const piB = msm(G2, key.queryB2, witness).add(key.vkBeta2)
  .add(key.vkDelta2.multiplyUnsafe(s))
const b1 = msm(G1, key.queryB1, witness).add(key.vkBeta1)
  .add(key.vkDelta1.multiplyUnsafe(s))
const piC = msm(G1, key.queryC, witness.slice(key.nPublic + 1))
  .add(msm(G1, key.hExps, h))
  .add(piA.multiplyUnsafe(s))
  .add(b1.multiplyUnsafe(r))
  .add(key.vkDelta1.multiplyUnsafe((order - r * s % order) % order))
const word = value => value.toString(16).padStart(64, '0')
const bAffine = piB.toAffine()
const solidityHex = '0x' + [piA.toAffine().x, piA.toAffine().y,
  bAffine.x.c1, bAffine.x.c0, bAffine.y.c1, bAffine.y.c0,
  piC.toAffine().x, piC.toAffine().y].map(word).join('')

const msmCases = [
  { group: 'g1', points: [point1(2), point1(3), G1.ZERO, point1(5)],
    scalars: [7n, 11n, 13n, 17n] },
  { group: 'g1', points: [G1.ZERO, point1(5)], scalars: [0n, order - 5n] },
  { group: 'g2', points: [point2(2), point2(3), G2.ZERO, point2(5)],
    scalars: [7n, 11n, 13n, 17n] },
  { group: 'g2', points: [G2.ZERO, point2(5)], scalars: [0n, order - 5n] },
].map(test => ({
  group: test.group,
  points: test.points.map(test.group === 'g1' ? encode1 : encode2),
  scalars: test.scalars.map(String),
  result: (test.group === 'g1' ? encode1 : encode2)
    (msm(test.group === 'g1' ? G1 : G2, test.points, test.scalars)),
}))

const windowCases = [
  { group: 'g1', count: 96, scalar: 3n },
  { group: 'g1', count: 2050, scalar: 1n },
  { group: 'g2', count: 96, scalar: 2n },
].map(item => ({ group: item.group, count: item.count,
  scalar: item.scalar.toString(),
  result: (item.group === 'g1' ? encode1 : encode2)
    ((item.group === 'g1' ? point1 : point2)(BigInt(item.count) * item.scalar)) }))

const output = JSON.stringify({
  source: 'pinned tornado-cli-new-era micro-zk-proofs 0.3.1 Groth16 formula and noble BN254',
  scalarOrder: order.toString(),
  msmCases,
  windowCases,
  assembly: {
    key: {
      nPublic: key.nPublic,
      vkAlpha1: encode1(key.vkAlpha1), vkBeta1: encode1(key.vkBeta1),
      vkDelta1: encode1(key.vkDelta1), vkBeta2: encode2(key.vkBeta2),
      vkDelta2: encode2(key.vkDelta2),
      queryA: key.queryA.map(encode1), queryB1: key.queryB1.map(encode1),
      queryB2: key.queryB2.map(encode2), queryC: key.queryC.map(encode1),
      hExps: key.hExps.map(encode1),
    },
    witness: witness.map(String), h: h.map(String), r: r.toString(), s: s.toString(),
    result: { piA: encode1(piA), piB: encode2(piB), piC: encode1(piC),
      solidityHex,
      publicSignals: witness.slice(1, key.nPublic + 1).map(String) },
  },
}, null, 2) + '\n'

const fixture = resolve(root, 'fixtures/groth16-msm-vectors.json')
if (process.argv.includes('--check')) {
  if (readFileSync(fixture, 'utf8') !== output)
    throw new Error('Groth16 MSM vectors changed')
  console.log('PASS: 4 noble MSM, 3 windowed MSM, and 1 Solidity proof vector')
} else {
  writeFileSync(fixture, output)
  console.log('Wrote four MSM, three windowed MSM, and one Solidity proof vector')
}
