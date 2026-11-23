import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { gunzipSync } from 'node:zlib'

// Development-only offline check of every Classic verification-key point
// against an immutable, vendored MIT-licensed Verifier.sol source snapshot.
// The proving key independently checks the three points it contains.
const expectedDigest = '8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af'
const expectedVkFixtureDigest = '2a0fb8adf35e96d4b553378dce9d81bf765c0369ec1caaae5b6af4639165327a'
const sourceCommit = '1ef6a263ac6a0e476d063fcb269a9df65a1bd56a'
const sourceDigest = 'a2fd9a12dc008ae95e1f9da2968e7d017617e804f22aa0491d2e8a91d965a824'
const fpPrime = 21888242871839275222246405745257275088696311157297823662689037894645226208583n
const montgomeryInverse = 20988524275117001072002809824448087578619730785600314334253784976379291040311n
const key = gunzipSync(readFileSync('assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz'))
const digest = createHash('sha256').update(key).digest('hex')
if (digest !== expectedDigest) throw Error('Pinned proving-key digest differs')
const vkBytes = readFileSync('fixtures/tornado-classic-verifying-key.json')
if (createHash('sha256').update(vkBytes).digest('hex') !== expectedVkFixtureDigest)
  throw Error('Classic Solidity VK fixture has changed from the reviewed snapshot')
const vk = JSON.parse(vkBytes)
if (vk.sourceSnapshotDate !== '2026-11-22' || vk.sourceCommit !== sourceCommit ||
    vk.sourceSha256 !== sourceDigest ||
    vk.source !== `https://github.com/tornadocash/tornado-core/blob/${sourceCommit}/contracts/Verifier.sol`)
  throw Error('Classic Solidity source/revision metadata changed')
const sourceBytes = readFileSync('fixtures/tornado-classic-Verifier.sol')
if (createHash('sha256').update(sourceBytes).digest('hex') !== sourceDigest)
  throw Error('Pinned immutable Classic Solidity source bytes changed')
const source = sourceBytes.toString('utf8')
const keyStart = source.indexOf('function verifyingKey()')
const keyEnd = source.indexOf('function verifyProof(', keyStart)
if (keyStart < 0 || keyEnd <= keyStart) throw Error('Classic Solidity verifier key function missing')
const keySource = source.slice(keyStart, keyEnd)
const exact = (name, pattern) => {
  const matches = [...keySource.matchAll(pattern)]
  if (matches.length !== 1) throw Error(`Expected one Classic Solidity ${name} assignment`)
  return matches[0].slice(1)
}
const g1Source = name => exact(name, new RegExp(
  `vk\\.${name}\\s*=\\s*Pairing\\.G1Point\\(uint256\\((\\d+)\\),\\s*uint256\\((\\d+)\\)\\)`, 'g'))
const g2Source = name => {
  const [x1, x0, y1, y0] = exact(name, new RegExp(
    `vk\\.${name}\\s*=\\s*Pairing\\.G2Point\\(\\[uint256\\((\\d+)\\),\\s*uint256\\((\\d+)\\)\\],\\s*\\[uint256\\((\\d+)\\),\\s*uint256\\((\\d+)\\)\\]\\)`, 'g'))
  return [[x0, x1], [y0, y1]]
}
for (const name of ['alpha1', 'beta2', 'gamma2', 'delta2']) {
  const fromSource = name === 'alpha1' ? g1Source('alfa1') : g2Source(name)
  if (JSON.stringify(fromSource) !== JSON.stringify(vk[name]))
    throw Error(`Classic ${name} differs from pinned immutable Verifier.sol`)
}
if (!Array.isArray(vk.IC) || vk.IC.length !== 7)
  throw Error('Classic IC fixture must contain exactly seven points')
for (let i = 0; i < 7; i++) {
  if (JSON.stringify(g1Source(`IC\\[${i}\\]`)) !== JSON.stringify(vk.IC[i]))
    throw Error(`Classic IC[${i}] differs from pinned immutable Verifier.sol`)
}
const fp = offset => {
  const bytes = key.subarray(offset,offset+32)
  if (bytes.length !== 32) throw Error('Truncated proving-key coordinate')
  const encoded = BigInt('0x'+Buffer.from(bytes).reverse().toString('hex'))
  if (encoded >= fpPrime) throw Error('Noncanonical proving-key Montgomery residue')
  return ((encoded*montgomeryInverse)%fpPrime).toString()
}
const g1 = offset => [fp(offset),fp(offset+32)]
const g2 = offset => [[fp(offset),fp(offset+32)],[fp(offset+64),fp(offset+96)]]
for (const [name,offset,decode] of [
  ['alpha1',40,g1],['beta2',232,g2],['delta2',360,g2],
]) {
  if (JSON.stringify(decode(offset)) !== JSON.stringify(vk[name]))
    throw Error(`Pinned proving-key ${name} differs from Classic Verifier.sol`)
}
console.log('PASS: complete Classic VK matches immutable Solidity source; proving-key alpha1, beta2, delta2 match')
