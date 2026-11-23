import { readFileSync, writeFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const source = resolve(root, '../tornado-cli-new-era')
const { bn254 } = await import(pathToFileURL(resolve(source,
  'node_modules/@noble/curves/bn254.js')).href)
const order = bn254.fields.Fr.ORDER
const base = bn254.G2.Point.BASE
const scalars = [0n, 1n, 2n, 3n, 5n, 6n, 7n, 17n, 12345n, order - 5n]
const point = scalar => {
  const value = base.multiplyUnsafe(scalar % order)
  if (value.equals(bn254.G2.Point.ZERO)) return null
  const { x, y } = value.toAffine()
  return { x0: x.c0.toString(), x1: x.c1.toString(),
    y0: y.c0.toString(), y1: y.c1.toString() }
}
const fixture = {
  source: 'pinned tornado-cli-new-era @noble/curves BN254 G2 public vectors',
  scalarOrder: order.toString(),
  basePrime: bn254.fields.Fp.ORDER.toString(),
  scalars: scalars.map(scalar => ({ scalar: scalar.toString(), result: point(scalar) })),
  additions: [[2n, 3n], [3n, 3n], [0n, 5n], [5n, order - 5n]]
    .map(([left, right]) => ({ left: left.toString(), right: right.toString(),
      result: point(left + right) })),
}
const output = JSON.stringify(fixture, null, 2) + '\n'
const path = resolve(root, 'fixtures/bn254-g2-vectors.json')
if (process.argv.includes('--check')) {
  if (readFileSync(path, 'utf8') !== output) throw new Error('BN254 G2 vectors changed')
  console.log('PASS: BN254 G2 vectors match pinned noble implementation')
} else {
  writeFileSync(path, output)
  console.log('Wrote pinned BN254 G2 vectors')
}
