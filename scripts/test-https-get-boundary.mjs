import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = fileURLToPath(new URL('../', import.meta.url))
const run = (command, args) => {
  const result = spawnSync(command, args, { cwd: root, encoding: 'utf8',
    timeout: 30000, maxBuffer: 1024 * 1024 })
  if (result.error || result.status !== 0) {
    throw new Error(`${command} failed: ${result.error ?? result.stderr}`)
  }
  return result.stdout.trim()
}
const prefix = run('lean', ['--print-prefix'])
const temp = mkdtempSync(join(tmpdir(), 'tornado-https-get-c-'))
try {
  const binary = join(temp, 'boundary-test')
  run('/usr/bin/cc', [`-I${join(prefix, 'include')}`, '-std=c11',
    '-Wall', '-Wextra', '-Werror', 'native/https_get_boundary_test.c',
    '-lcurl', '-o', binary])
  console.log(run(binary, []))
} finally {
  rmSync(temp, { recursive: true, force: true })
}
