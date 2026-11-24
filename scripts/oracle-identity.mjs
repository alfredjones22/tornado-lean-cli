import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'
import { existsSync, lstatSync, readFileSync, readdirSync, writeFileSync } from 'node:fs'
import { resolve, relative, sep } from 'node:path'
import { fileURLToPath } from 'node:url'

// Development oracles only. The CLI runtime does not load this module.
export const repository = fileURLToPath(new URL('../', import.meta.url))
export const oracleSource = resolve(process.env.TORNADO_TS_CLI ?? resolve(repository, '../tornado-cli-new-era'))
export const oracleCommit = 'a24d5f5e89d1f2486a031b1e5e8b1a92e81e1326'
export const oracleSdkVersion = '0.1.0-alpha.40'
const fixturePath = resolve(repository, 'fixtures/typescript-oracle-identity.json')
const hash = bytes => createHash('sha256').update(bytes).digest('hex')
const json = file => JSON.parse(readFileSync(file, 'utf8'))
const packagePaths = [
  'node_modules/@kohaku-eth/tornado-cash',
  'node_modules/@kohaku-eth/mimc-tree',
  'node_modules/@kohaku-eth/plugins',
  'node_modules/@kohaku-eth/provider',
  'node_modules/@noble/curves',
  'node_modules/micro-zk-proofs',
  'node_modules/micro-zk-proofs/node_modules/@noble/curves',
  'node_modules/viem',
]

// Hash all package-owned bytes, including circuit files. Nested dependencies
// have their own lock entries and selected oracle packages have separate trees.
export function packageTree(directory) {
  const files = []
  const visit = current => {
    for (const entry of readdirSync(current).sort()) {
      if (entry === 'node_modules') continue
      const path = resolve(current, entry)
      const info = lstatSync(path)
      if (info.isSymbolicLink()) throw new Error(`Oracle package contains a symlink: ${path}`)
      if (info.isDirectory()) visit(path)
      else if (info.isFile()) files.push([relative(directory, path).split(sep).join('/'), hash(readFileSync(path))])
      else throw new Error(`Oracle package contains a non-file: ${path}`)
    }
  }
  visit(directory)
  return { fileCount: files.length, sha256: hash(JSON.stringify(files)) }
}

function snapshot(source) {
  const git = args => execFileSync('git', args, { cwd: source, encoding: 'utf8' }).trim()
  if (git(['rev-parse', 'HEAD']) !== oracleCommit || git(['status', '--porcelain=v1']))
    throw new Error('TypeScript oracle must be the clean pinned CLI commit')
  const pkg = json(resolve(source, 'package.json'))
  const lock = json(resolve(source, 'package-lock.json'))
  const sdk = json(resolve(source, packagePaths[0], 'package.json'))
  if (pkg.dependencies['@kohaku-eth/tornado-cash'] !== oracleSdkVersion || sdk.version !== oracleSdkVersion)
    throw new Error('Pinned TypeScript SDK version changed')
  const sdkLock = lock.packages[packagePaths[0]]
  if (sdkLock.version !== oracleSdkVersion || typeof sdkLock.integrity !== 'string')
    throw new Error('Pinned TypeScript SDK lock entry changed')
  return {
    schemaVersion: 1, sourceCommit: oracleCommit, sdkVersion: oracleSdkVersion,
    sdkTarballIntegrity: sdkLock.integrity,
    files: Object.fromEntries(['package.json', 'package-lock.json', 'dist/index.js'].map(path =>
      [path, hash(readFileSync(resolve(source, path)))])),
    packages: Object.fromEntries(packagePaths.map(path => [path, {
      version: json(resolve(source, path, 'package.json')).version,
      ...packageTree(resolve(source, path)),
    }])),
  }
}

export function assertOracleIdentity(source = oracleSource) {
  const pinned = json(fixturePath)
  const actual = snapshot(source)
  if (JSON.stringify(actual) !== JSON.stringify(pinned))
    throw new Error('TypeScript oracle package/lock/build/installed dependency bytes differ from the pinned identity')
  return actual
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  if (process.argv.length !== 3 || !['--write', '--check'].includes(process.argv[2]))
    throw new Error('Use --write or --check')
  if (process.argv[2] === '--write') {
    if (!existsSync(resolve(oracleSource, 'dist/index.js'))) throw new Error('Build the pinned TypeScript oracle first')
    writeFileSync(fixturePath, JSON.stringify(snapshot(oracleSource), null, 2) + '\n')
  } else assertOracleIdentity()
  console.log('PASS: pinned alpha.40 CLI source, lockfile, build and eight installed oracle package trees')
}
