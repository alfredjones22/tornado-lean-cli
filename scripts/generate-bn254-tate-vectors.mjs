import { readFileSync, writeFileSync } from 'node:fs'
import { pathToFileURL } from 'node:url'

// Development-only independent arithmetic oracle. Noble is never loaded by Lean.
const noble = process.env.NOBLE_BN254_JS ??
  `${process.cwd()}/../tornado-cli-new-era/node_modules/micro-zk-proofs/node_modules/@noble/curves/bn254.js`
const { bn254 } = await import(pathToFileURL(noble).href)
const { Fp12, Fp, Fr } = bn254.fields
const z2 = { c0: 0n, c1: 0n }
const fp2 = n => ({ c0: n, c1: 0n })
const fp6 = (c0=z2,c1=z2,c2=z2) => ({ c0,c1,c2 })
const embFp = n => ({ c0: fp6(fp2(n)), c1: fp6() })
const embFp2 = a => ({ c0: fp6(a), c1: fp6() })
const embG1 = p => ({ x: embFp(p.x), y: embFp(p.y) })
const embG2 = q => ({ x: { c0: fp6(z2,q.x), c1: fp6() },
  y: { c0: fp6(), c1: fp6(z2,q.y) } })
const flat6 = v => [v.c0.c0,v.c0.c1,v.c1.c0,v.c1.c1,v.c2.c0,v.c2.c1]
const flat12 = v => [...flat6(v.c0),...flat6(v.c1)].map(x => x.toString())
const eq = Fp12.eql.bind(Fp12), sub = Fp12.sub.bind(Fp12)
const mul = Fp12.mul.bind(Fp12), sqr = Fp12.sqr.bind(Fp12)
const inv = Fp12.inv.bind(Fp12), neg = Fp12.neg.bind(Fp12)
const divide = (a,b) => mul(a, inv(b))

function lineAndSum(r,s,t) {
  if (eq(r.x,s.x) && eq(r.y,neg(s.y))) {
    return [sub(t.x,r.x), null]
  }
  const slope = eq(r.x,s.x) && eq(r.y,s.y)
    ? divide(mul(embFp(3n),sqr(r.x)),mul(embFp(2n),r.y))
    : divide(sub(s.y,r.y),sub(s.x,r.x))
  const x3 = sub(sub(sqr(slope),r.x),s.x)
  const y3 = sub(mul(slope,sub(r.x,x3)),r.y)
  const line = sub(sub(t.y,r.y),mul(slope,sub(t.x,r.x)))
  return [divide(line,sub(t.x,x3)),{x:x3,y:y3}]
}

function reducedTate(p,q) {
  const P = embG1(p), Q = embG2(q)
  const bits = Fr.ORDER.toString(2)
  let R = Q, f = Fp12.ONE
  for (const bit of bits.slice(1)) {
    const [gD,R2] = lineAndSum(R,R,P)
    R = R2; f = mul(sqr(f),gD)
    if (bit === '1') {
      const [gA,R3] = lineAndSum(R,Q,P)
      R = R3; f = mul(f,gA)
    }
  }
  if (R !== null) throw Error('Miller accumulator failed to reach infinity')
  return Fp12.pow(f,(Fp.ORDER ** 12n-1n)/Fr.ORDER)
}

const p = bn254.G1.Point.BASE
const q = bn254.G2.Point.BASE
const e = reducedTate(p.toAffine(),q.toAffine())
if (eq(e,Fp12.ONE) || !eq(Fp12.pow(e,Fr.ORDER),Fp12.ONE))
  throw Error('Reduced Tate result is not nontrivial r-torsion')
const eP2 = reducedTate(p.multiply(2n).toAffine(),q.toAffine())
const eQ2 = reducedTate(p.toAffine(),q.multiply(2n).toAffine())
if (!eq(eP2,sqr(e)) || !eq(eQ2,sqr(e)))
  throw Error('Reduced Tate bilinearity failed')
const { Fp2 } = bn254.fields
const x = { c0: 1n, c1: 0n }
const y = {
  c0: 3610091866386166428467545612961983990332663701371483510632385378352395651980n,
  c1: 15975588672102553735566230729081043132501226101599136527557730645158523614371n,
}
const twistB = {
  c0: 19485874751759354771024239261021720505790618469301721065564631296452457478373n,
  c1: 266929791119991161246907387137283842545076965332900288569378510910307636690n,
}
if (!Fp2.eql(Fp2.sqr(y), Fp2.add(Fp2.mul(Fp2.sqr(x), x), twistB)))
  throw Error('Pinned non-subgroup point is off the twist')
if (bn254.G2.Point.fromAffine({x,y}).isTorsionFree())
  throw Error('Pinned non-subgroup point unexpectedly has prime order')

const vector = {
  source: '@noble/curves@2.2.0 Fp12 arithmetic and generator points; independent reduced Tate reference',
  basePrime: Fp.ORDER.toString(),
  scalarPrime: Fr.ORDER.toString(),
  generatorPairing: flat12(e),
  doubleG1Pairing: flat12(eP2),
  doubleG2Pairing: flat12(eQ2),
  nonSubgroupG2: [x.c0,x.c1,y.c0,y.c1].map(n => n.toString()),
}
const output = 'fixtures/bn254-tate-vectors.json'
const generated = JSON.stringify(vector,null,2)+'\n'
if (process.argv.includes('--check')) {
  if (readFileSync(output,'utf8') !== generated)
    throw Error('Pinned BN254 Tate vectors differ from noble oracle')
  console.log('PASS: three reduced Tate vectors and non-subgroup point match pinned noble')
} else {
  writeFileSync(output,generated)
  console.log('Wrote independent BN254 reduced Tate generator vectors')
}
