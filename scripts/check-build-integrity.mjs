#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { constants, closeSync, fstatSync, openSync, readSync, lstatSync, realpathSync } from 'node:fs';
import { isAbsolute, join, resolve, sep } from 'node:path';

// Deliberately independent of the candidate CLI, worker, generator, Lake, and
// native libraries. Candidates are opened as data and are never executed.
const fail = message => { throw new Error(message); };
const check = (condition, message) => { if (!condition) fail(message); };
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const hashPattern = /^[a-f0-9]{64}$/;
function safeRelative(value) {
  check(typeof value === 'string' && value.length > 0 && value.length <= 4096 &&
    !isAbsolute(value) && !value.includes('\\') && !value.includes('\0') &&
    value.split('/').every(part => /^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(part)), 'Unsafe manifest asset path');
  return value;
}
function regularHash(file, expectedSize, role) {
  const entry=lstatSync(file);
  check(!entry.isSymbolicLink(), 'Refusing a symbolic-link candidate');
  check(entry.isFile(), 'Candidate must be a nonempty regular file');
  const fd = openSync(file, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0) | (constants.O_NONBLOCK ?? 0));
  try {
    const before = fstatSync(fd, {bigint:true});
    check(before.isFile() && before.size > 0n && before.size <= BigInt(Number.MAX_SAFE_INTEGER), 'Candidate must be a nonempty regular file');
    check(before.size===BigInt(expectedSize),`${role} integrity mismatch: candidate size differs from trusted manifest`);
    const hash = createHash('sha256'), buffer = Buffer.allocUnsafe(1024 * 1024);
    let count;
    while ((count = readSync(fd, buffer, 0, buffer.length, null)) > 0) hash.update(buffer.subarray(0, count));
    const after = fstatSync(fd, {bigint:true});
    check(before.size === after.size && before.mtimeNs === after.mtimeNs && before.ctimeNs === after.ctimeNs,
      'Candidate changed while hashing');
    return {sha256:hash.digest('hex'), size:Number(after.size)};
  } finally { closeSync(fd); }
}
function readManifest(file) {
  const entry=lstatSync(file);
  check(entry.isFile() && !entry.isSymbolicLink() && entry.size>0 && entry.size<=16*1024*1024,
    'Invalid manifest size or type');
  const fd=openSync(file,constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0) | (constants.O_NONBLOCK ?? 0));
  try {
    const before=fstatSync(fd,{bigint:true});
    check(before.isFile() && before.size>0n && before.size<=16n*1024n*1024n,'Invalid manifest size or type');
    const bytes=Buffer.alloc(Number(before.size)+1);let used=0,n;
    while(used<bytes.length && (n=readSync(fd,bytes,used,bytes.length-used,null))>0) used+=n;
    const after=fstatSync(fd,{bigint:true});
    check(used===Number(before.size) && before.size===after.size && before.mtimeNs===after.mtimeNs &&
      before.ctimeNs===after.ctimeNs,'Manifest changed while reading');
    return bytes.subarray(0,used);
  } finally {closeSync(fd);}
}
function assetPath(root, relative) {
  const base = realpathSync(root), parts = safeRelative(relative).split('/');
  let current = base;
  for (const part of parts) {
    current = join(current, part);
    check(!lstatSync(current).isSymbolicLink(), 'Refusing a symbolic-link asset path');
  }
  check(current.startsWith(base + sep), 'Asset path escapes candidate root');
  return current;
}
function record(value, role) {
  check(value && typeof value === 'object' && !Array.isArray(value) &&
    hashPattern.test(value.sha256) && Number.isSafeInteger(value.size) && value.size > 0,
    `Invalid ${role} integrity record`);
  return value;
}
function args(argv) {
  const result = {};
  for (let i=0;i<argv.length;i+=2) {
    check(['--manifest','--manifest-sha256','--cli','--worker','--asset-root'].includes(argv[i]) &&
      argv[i+1] && !argv[i+1].startsWith('--') && !Object.hasOwn(result,argv[i]), 'Invalid or duplicate integrity argument');
    result[argv[i]]=argv[i+1];
  }
  for (const name of ['--manifest','--manifest-sha256','--cli','--worker','--asset-root'])
    check(Object.hasOwn(result,name), `Missing ${name}`);
  return result;
}
try {
  const options=args(process.argv.slice(2));
  check(hashPattern.test(options['--manifest-sha256']), 'Trusted manifest SHA256 must be 64 lowercase hex digits');
  const bytes=readManifest(resolve(options['--manifest']));
  check(bytes.length <= 16 * 1024 * 1024, 'Manifest exceeds size limit');
  check(digest(bytes)===options['--manifest-sha256'], 'Trusted manifest digest mismatch');
  const manifest=JSON.parse(bytes.toString('utf8'));
  check(manifest.schemaVersion===1 && manifest.kind==='tornado-lean-build-provenance' &&
    manifest.verification?.status==='PASS_WITH_LIMITATIONS', 'Unsupported or unverified manifest');
  const cli=record(manifest.artifacts?.cli,'CLI'), worker=record(manifest.artifacts?.worker,'worker');
  check(Array.isArray(manifest.assets) && manifest.assets.length > 0 && manifest.assets.length <= 64, 'Invalid asset inventory');
  const seen=new Set();
  for (const asset of manifest.assets) {
    record(asset,'asset'); safeRelative(asset.path);
    check(!seen.has(asset.path), 'Duplicate manifest asset'); seen.add(asset.path);
  }
  const verify=(candidate, expected, role) => {
    const actual=regularHash(candidate,expected.size,role);
    check(actual.size===expected.size && actual.sha256===expected.sha256, `${role} integrity mismatch`);
  };
  verify(resolve(options['--cli']),cli,'CLI');
  verify(resolve(options['--worker']),worker,'Worker');
  for (const asset of manifest.assets) verify(assetPath(options['--asset-root'],asset.path),asset,`Asset ${asset.path}`);
  console.log(`PASS: trusted-manifest integrity matched CLI, worker and ${manifest.assets.length} assets; no candidate was executed`);
} catch (error) {
  console.error(`Build integrity failed: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode=1;
}
