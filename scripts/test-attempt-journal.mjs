import { spawnSync } from 'node:child_process'
import { chmodSync, mkdtempSync, rmSync } from 'node:fs'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const directory = mkdtempSync(join(root, '.attempt-journal-test-'))
try {
  chmodSync(directory, 0o700)
  const binary = resolve(root, '.lake/build/bin/attempt_journal_test')
  const result = spawnSync(binary, [directory], { encoding: 'utf8', timeout: 30000 })
  if (result.error || result.status !== 0) {
    throw new Error(`Attempt journal test failed: ${result.error ?? ''}\n${result.stdout}\n${result.stderr}`)
  }
  process.stdout.write(result.stdout)
} finally {
  rmSync(directory, { recursive: true, force: true })
}
