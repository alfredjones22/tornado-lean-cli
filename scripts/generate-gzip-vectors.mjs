#!/usr/bin/env node
// Development-only gzip vectors from Node's zlib. Runtime decoding is Lean.
import { gzipSync, constants } from 'node:zlib'
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
const fixturePath = join(root, 'fixtures/gzip-vectors.json')
const checksum = data => createHash('sha256').update(data).digest('hex')

function crc32(data) {
  let value = 0xffffffff
  for (const byte of data) {
    value ^= byte
    for (let i = 0; i < 8; i++)
      value = (value >>> 1) ^ (value & 1 ? 0xedb88320 : 0)
  }
  return (value ^ 0xffffffff) >>> 0
}

function optionalHeader(gzip) {
  const header = Buffer.from(gzip.subarray(0, 10))
  header[3] = 0x1e // FEXTRA, FNAME, FCOMMENT, FHCRC
  const extra = Buffer.from([3, 0, 0x41, 0, 0xff])
  const name = Buffer.from('public-test-vector\0', 'utf8')
  const comment = Buffer.from('Lean gzip header test\0', 'utf8')
  const prefix = Buffer.concat([header, extra, name, comment])
  const headerCrc = Buffer.alloc(2)
  headerCrc.writeUInt16LE(crc32(prefix) & 0xffff)
  return Buffer.concat([prefix, headerCrc, gzip.subarray(10)])
}

function emptyFixedBlocks(count) {
  const reference = gzipSync(Buffer.alloc(0), { mtime: 0 })
  const bits = Buffer.alloc(Math.ceil(count * 10 / 8))
  for (let block = 0; block < count; block++) {
    const at = block * 10
    // BFINAL, BTYPE=01, then fixed EOB symbol 256 (seven zero bits).
    if (block === count - 1) bits[at >> 3] |= 1 << (at & 7)
    bits[(at + 1) >> 3] |= 1 << ((at + 1) & 7)
  }
  return Buffer.concat([reference.subarray(0, 10), bits,
    reference.subarray(reference.length - 8)])
}

const payloads = [
  ['empty', Buffer.alloc(0), { level: 6 }],
  ['stored', Buffer.from('stored block: \x00\xff and some UTF-8 ☔', 'utf8'), { level: 0 }],
  ['fixed', Buffer.from('The quick brown fox jumps over the lazy dog. '.repeat(9)),
    { level: 9, strategy: constants.Z_FIXED }],
  ['dynamic', Buffer.from(('Tornado privacy requires durable note reservations. '.repeat(64) +
    'BN254 Groth16 witness, Merkle path and journal recovery. '.repeat(31))), { level: 9 }],
  ['optional', Buffer.from('optional gzip headers and CRC16'), { level: 6 }],
  ['three-fixed-blocks', Buffer.alloc(0), { level: 6 }],
]

const cases = payloads.map(([name, raw, options]) => {
  const base = gzipSync(raw, { ...options, mtime: 0 })
  const gzip = name === 'optional' ? optionalHeader(base) :
    name === 'three-fixed-blocks' ? emptyFixedBlocks(3) : base
  return { name, gzipHex: gzip.toString('hex'), rawHex: raw.toString('hex'),
    compressedBytes: gzip.length, rawBytes: raw.length,
    firstBlockType: (base[10] >> 1) & 3,
    crc32: crc32(raw), sha256: checksum(raw) }
})

const output = JSON.stringify({ cases,
  tooManyFixedBlocksHex: emptyFixedBlocks(4097).toString('hex') }, null, 2) + '\n'
if (process.argv[2] === '--write') {
  writeFileSync(fixturePath, output)
  console.log(`Wrote ${cases.length} gzip/DEFLATE vectors`)
} else if (process.argv[2] === '--check') {
  if (readFileSync(fixturePath, 'utf8') !== output)
    throw new Error('Gzip vectors differ from pinned development fixture')
  console.log(`PASS: ${cases.length} gzip/DEFLATE vectors match Node zlib`)
} else {
  throw new Error('Use --write or --check')
}
