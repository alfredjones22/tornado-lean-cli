import { readFileSync, writeFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { pathToFileURL } from 'node:url'

// Development-only finite oracle from the pinned Noble implementation.
const noble = process.env.NOBLE_BN254_JS ??
  `${process.cwd()}/../tornado-cli-new-era/node_modules/micro-zk-proofs/node_modules/@noble/curves/bn254.js`
const { bn254 } = await import(pathToFileURL(noble).href)
const { Fp6, Fp12 } = bn254.fields
const p = bn254.fields.Fp.ORDER
const toField = limbs => ({
  c0: { c0: BigInt(limbs[0]), c1: BigInt(limbs[1]) },
  c1: { c0: BigInt(limbs[2]), c1: BigInt(limbs[3]) },
  c2: { c0: BigInt(limbs[4]), c1: BigInt(limbs[5]) },
})
const toFp12 = limbs => ({ c0: toField(limbs.slice(0, 6)),
  c1: toField(limbs.slice(6, 12)) })
const flat6 = v => [v.c0.c0, v.c0.c1, v.c1.c0, v.c1.c1, v.c2.c0, v.c2.c1]
const flat12 = v => [...flat6(v.c0), ...flat6(v.c1)]
const decimal = a => a.map(v => v.toString())
const hexNumber = (label, i) => BigInt('0x' + createHash('sha256').update(label + i).digest('hex')) % p
const samples = [
  { a: Array.from({ length: 12 }, (_, i) => BigInt(i + 1)),
    b: Array.from({ length: 12 }, (_, i) => BigInt(i + 13)) },
  { a: [0n, p - 1n, 2n, 0n, 7n, 9n, 1n, 0n, p - 2n, 5n, 0n, 10n],
    b: [3n, 4n, 0n, p - 3n, 1n, 11n, 8n, 2n, 0n, 0n, 17n, p - 4n] },
  { a: Array.from({ length: 12 }, (_, i) => hexNumber('a', i)),
    b: Array.from({ length: 12 }, (_, i) => hexNumber('b', i)) },
]
const vectors = samples.map(({a,b}) => {
  const a6 = toField(a.slice(0, 6))
  const b6 = toField(b.slice(0, 6))
  const a12 = toFp12(a)
  const b12 = toFp12(b)
  return {
    a: decimal(a), b: decimal(b),
    fp6Add: decimal(flat6(Fp6.add(a6,b6))),
    fp6Mul: decimal(flat6(Fp6.mul(a6,b6))),
    fp6Inverse: decimal(flat6(Fp6.inv(a6))),
    fp12Mul: decimal(flat12(Fp12.mul(a12,b12))),
    fp12Inverse: decimal(flat12(Fp12.inv(a12))),
    fp12Pow12345: decimal(flat12(Fp12.pow(a12,12345n))),
  }
})
const fixture = {
  source: '@noble/curves@2.2.0 bn254 Fp6/Fp12 nested under micro-zk-proofs@0.3.1',
  basePrime: p.toString(),
  vectors,
}
const output = 'fixtures/bn254-tower-vectors.json'
const generated = JSON.stringify(fixture,null,2) + '\n'
if (process.argv.includes('--check')) {
  if (readFileSync(output,'utf8') !== generated)
    throw Error('Pinned BN254 tower vectors differ from noble oracle')
  console.log('PASS: three BN254 tower vectors match pinned noble')
} else {
  writeFileSync(output,generated)
  console.log('Wrote 3 independent BN254 extension-field vectors')
}
