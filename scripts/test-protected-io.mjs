import { spawnSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, writeFileSync, chmodSync, symlinkSync,
  linkSync, rmSync, statSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const testRoot = mkdtempSync(join(root, '.private-io-test-'))
try {
  chmodSync(testRoot, 0o700)
  writeFileSync(join(testRoot, 'public'), 'visible', { mode: 0o644 })
  chmodSync(join(testRoot, 'public'), 0o644)
  writeFileSync(join(testRoot, 'linked-target'), 'linked', { mode: 0o600 })
  linkSync(join(testRoot, 'linked-target'), join(testRoot, 'hardlink'))
  symlinkSync(join(testRoot, 'linked-target'), join(testRoot, 'symlink'))
  symlinkSync(testRoot, join(testRoot, 'parent-symlink'))
  const binary = resolve(root, '.lake/build/bin/protected_io_test')
  const result = spawnSync(binary, [testRoot], { encoding: 'utf8', timeout: 30000 })
  if (result.error || result.status !== 0) {
    throw new Error(`Protected IO test failed: ${result.error ?? ''}\n${result.stdout}\n${result.stderr}`)
  }
  if (statSync(join(testRoot, 'private')).mode & 0o077) {
    throw new Error('Private file has group/other permissions')
  }
  process.stdout.write(result.stdout)
  if (process.platform === 'darwin') {
    const aclParent = join(testRoot, 'acl-parent')
    mkdirSync(aclParent, { mode: 0o700 })
    chmodSync(aclParent, 0o700)
    const aclLeaf = join(testRoot, 'acl-leaf')
    writeFileSync(aclLeaf, 'private note', { mode: 0o600 })
    chmodSync(aclLeaf, 0o600)
    for (const [path, rule] of [
      [aclParent, 'everyone allow read,file_inherit'],
      [aclLeaf, 'everyone allow read'],
    ]) {
      const grant = spawnSync('/bin/chmod', ['+a', rule, path], { encoding: 'utf8' })
      if (grant.error || grant.status !== 0) {
        throw new Error(`Could not set test ACL: ${grant.error ?? grant.stderr}`)
      }
    }
    if ((statSync(aclParent).mode & 0o777) !== 0o700 ||
        (statSync(aclLeaf).mode & 0o777) !== 0o600) {
      throw new Error('ACL fixture changed POSIX permissions')
    }
    const aclResult = spawnSync(binary, [testRoot, 'acl'], { encoding: 'utf8', timeout: 30000 })
    if (aclResult.error || aclResult.status !== 0) {
      throw new Error(`Protected IO ACL test failed: ${aclResult.error ?? ''}\n${aclResult.stdout}\n${aclResult.stderr}`)
    }
    process.stdout.write(aclResult.stdout)
  }
} finally {
  rmSync(testRoot, { recursive: true, force: true })
}
