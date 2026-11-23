import { readFileSync, writeFileSync } from 'node:fs'
import { pathToFileURL } from 'node:url'

// Development-only independent proof-equation oracle. Noble is not a Lean CLI
// runtime dependency. The VK is checked against the pinned Classic Verifier.sol
// by check-classic-vk-provenance.mjs.
const root = process.cwd()
const fixtureDir = `${root}/fixtures`
const noble = process.env.NOBLE_BN254_JS ??
  `${root}/../tornado-cli-new-era/node_modules/micro-zk-proofs/node_modules/@noble/curves/bn254.js`
const { bn254 } = await import(pathToFileURL(noble).href)
const { Fp12, Fr } = bn254.fields
const vk = JSON.parse(readFileSync(`${fixtureDir}/tornado-classic-verifying-key.json`))
const proof = JSON.parse(readFileSync(`${root}/fixtures/groth16-full-public-proof.json`))
const beWords = (hex) => {
  const body = hex.startsWith('0x') ? hex.slice(2) : hex
  if (body.length !== 512) throw Error('Classic proof must have eight 32-byte words')
  return Array.from({length:8},(_,i) => BigInt(`0x${body.slice(i*64,(i+1)*64)}`))
}
const word = beWords(proof.solidityProofHex)
const g1 = coords => bn254.G1.Point.fromAffine({x:BigInt(coords[0]),y:BigInt(coords[1])})
const g2 = coords => bn254.G2.Point.fromAffine({
  x:{c0:BigInt(coords[0][0]),c1:BigInt(coords[0][1])},
  y:{c0:BigInt(coords[1][0]),c1:BigInt(coords[1][1])},
})
const A = bn254.G1.Point.fromAffine({x:word[0],y:word[1]})
const B = bn254.G2.Point.fromAffine({
  x:{c0:word[3],c1:word[2]},y:{c0:word[5],c1:word[4]},
})
const C = bn254.G1.Point.fromAffine({x:word[6],y:word[7]})
const alpha = g1(vk.alpha1), beta = g2(vk.beta2)
const gamma = g2(vk.gamma2), delta = g2(vk.delta2)
const IC = vk.IC.map(g1)
const signals = proof.publicSignals.map(x => BigInt(x))
if (signals.length !== 6 || signals.some(x => x >= Fr.ORDER))
  throw Error('Malformed public signal fixture')
const vkX = values => values.reduce((sum,s,i) => s === 0n ? sum : sum.add(IC[i+1].multiply(s)),IC[0])
const equation = values => {
  const points = [[A.negate(),B],[alpha,beta],[vkX(values),gamma],[C,delta]]
  return points.reduce((product,[p,q]) => Fp12.mul(product,bn254.pairing(p,q)),Fp12.ONE)
}
const valid = Fp12.eql(equation(signals),Fp12.ONE)
const tamperedSignals = signals.map((_,i) => {
  const changed = signals.slice(); changed[i] += 1n
  if (changed[i] >= Fr.ORDER) throw Error('Tampered signal exceeds Fr')
  return changed
})
const tamperedAccepted = tamperedSignals.map(values => Fp12.eql(equation(values),Fp12.ONE))
if (!valid || tamperedAccepted.some(Boolean))
  throw Error(`Classic proof equation oracle unexpected: valid=${valid}, tampered=${tamperedAccepted}`)
const affine = p => [p.toAffine().x.toString(),p.toAffine().y.toString()]
const generated = JSON.stringify({
  sourceProof: 'fixtures/groth16-full-public-proof.json',
  sourceVerifyingKey: vk.source,
  oracle: '@noble/curves@2.2.0 BN254 optimal Ate pairing',
  accepted: valid,
  tamperedSignalAccepted: tamperedAccepted,
  vkX: affine(vkX(signals)),
  tamperedVkXBySignal: tamperedSignals.map(values => affine(vkX(values))),
},null,2)+'\n'
const output = `${fixtureDir}/tornado-classic-proof-equation.json`
if (process.argv.includes('--check')) {
  if (readFileSync(output,'utf8') !== generated)
    throw Error('Pinned Classic proof-equation fixture differs from noble oracle')
} else {
  writeFileSync(output,generated)
}
console.log('PASS: noble accepts pinned Classic proof and rejects all six changed public signals')
