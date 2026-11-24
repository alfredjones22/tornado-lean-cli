// Deliberately has no RPC URL, fork, key, signing, or broadcast option.
// Every transaction goes to a fresh owned loopback Anvil with synthetic funds.
import assert from 'node:assert/strict'
import { execFileSync, spawn } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { createServer } from 'node:net'
import { join } from 'node:path'
import { setTimeout as delay } from 'node:timers/promises'
import { buildLocalEvmFixtures, repository } from './build-local-evm-fixtures.mjs'

const json = name => JSON.parse(readFileSync(join(repository, name), 'utf8'))
const word = value => BigInt(value).toString(16).padStart(64, '0')
const clean = value => value.replace(/^0x/, '')
const addressWord = value => clean(value).toLowerCase().padStart(64, '0')
const signatureCache = new Map()
const commandOptions = { encoding: 'utf8', env: { ...process.env, FOUNDRY_DISABLE_NIGHTLY_WARNING: '1' } }
function selector(signature) {
  if (!signatureCache.has(signature)) signatureCache.set(signature,
    execFileSync('cast', ['sig', signature], commandOptions).trim())
  return signatureCache.get(signature)
}
const calldata = (signature, ...values) => selector(signature) + values.map(word).join('')
const encode = (signature, ...values) => execFileSync('cast', ['calldata', signature, ...values.map(String)], commandOptions).trim()
const zero = '0x0000000000000000000000000000000000000000'
const built = buildLocalEvmFixtures()
let anvil
let output = ''
let requestNumber = 0
let assertions = 0
const check = (actual, expected, label) => { assert.equal(actual, expected, label); assertions++ }

try {
  assert.deepEqual(built.manifest, json('fixtures/evm/artifact-provenance.json'), 'pinned source/compiler/bytecode provenance')
  const server = createServer()
  await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve) })
  const port = server.address().port
  await new Promise(resolve => server.close(resolve))
  const rpcUrl = `http://127.0.0.1:${port}`
  anvil = spawn('anvil', ['--host', '127.0.0.1', '--port', String(port), '--chain-id', '31337', '--hardfork', 'cancun', '--silent'],
    { stdio: ['ignore', 'pipe', 'pipe'], env: commandOptions.env })
  anvil.stdout.on('data', chunk => { output += chunk })
  anvil.stderr.on('data', chunk => { output += chunk })
  const rpc = async (method, params = []) => {
    const response = await fetch(rpcUrl, { method: 'POST', headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ jsonrpc: '2.0', id: ++requestNumber, method, params }), signal: AbortSignal.timeout(15000) })
    const body = await response.json()
    if (body.error) throw new Error(`${method}: ${body.error.message}`)
    return body.result
  }
  let ready = false
  for (let attempt = 0; attempt < 100; attempt++) {
    if (anvil.exitCode !== null) throw new Error(`Anvil exited: ${output}`)
    try { ready = (await rpc('web3_clientVersion')).toLowerCase().includes('anvil'); if (ready) break } catch {}
    await delay(50)
  }
  if (!ready) throw new Error(`Owned loopback Anvil did not start: ${output}`)
  check(await rpc('eth_chainId'), '0x7a69', 'isolated synthetic chain')
  const accounts = await rpc('eth_accounts')
  const [owner, outsider, receiver, feeRecipient] = accounts
  const send = async (to, data, { from = owner, success = true, value = '0x0' } = {}) => {
    const hash = await rpc('eth_sendTransaction', [{ from, ...(to ? { to } : {}), data, value, gas: '0x1c9c380' }])
    for (let attempt = 0; attempt < 100; attempt++) {
      const receipt = await rpc('eth_getTransactionReceipt', [hash])
      if (receipt) { check(receipt.status, success ? '0x1' : '0x0', 'synthetic transaction status'); return receipt }
      await delay(25)
    }
    throw new Error('Synthetic transaction receipt timeout.')
  }
  const call = (to, data, from = owner) => rpc('eth_call', [{ to, from, data, gas: '0x1c9c380' }, 'latest'])
  const number = async (to, data) => BigInt(await call(to, data))
  const deploy = async (name, constructor = '') => (await send(null, built.artifacts[name].bytecode + constructor)).contractAddress

  const verifier = await deploy('Verifier')
  const proofFixtures = ['fixtures/groth16-full-public-proof.json', 'fixtures/groth16-relayer-public-proof.json',
    'fixtures/groth16-account-public-proof.json']
  for (const name of proofFixtures) {
    const fixture = json(name)
    const verifyData = signals => selector('verifyProof(bytes,uint256[6])') + word(224) +
      signals.map(word).join('') + word(clean(fixture.solidityProofHex).length / 2) + clean(fixture.solidityProofHex)
    check(BigInt(await call(verifier, verifyData(fixture.publicSignals))), 1n, `${name}: actual Classic Solidity verifier accepts`)
    for (let index = 0; index < 6; index++) {
      const changed = [...fixture.publicSignals]
      changed[index] = String(BigInt(changed[index]) + 1n)
      check(BigInt(await call(verifier, verifyData(changed))), 0n, `${name}: public signal ${index} binds`)
    }
  }

  const entryPoint = await deploy('ProbeEntryPoint')
  const factory = await deploy('SimpleAccountFactory', addressWord(entryPoint))
  const token = await deploy('ProbeToken')
  const pool = await deploy('ProbePool', addressWord(token))
  const recorder = await deploy('ProbeRecorder')
  const failure = await deploy('ProbeFailure')
  const salt = BigInt(json('fixtures/recovery-vectors.json').vectors[0].factorySalt)
  const predicted = await call(factory, calldata('getAddress(address,uint256)', owner, salt))
  const account = '0x' + predicted.slice(-40)
  const native = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tests/evm/Export.lean',
    owner, account, pool, token, recorder, failure, receiver, feeRecipient], { cwd: repository, encoding: 'utf8' }))
  check(native.callCount, 4, 'native independent decoder retained four ordered calls')
  await send(factory, native.factoryData)
  check((await call(account, selector('owner()'))).slice(-40).toLowerCase(), clean(owner).toLowerCase(), 'actual factory initializes actual account owner')
  await send(token, calldata('mint(address,uint256)', pool, 1000))
  await send(account, native.batch)
  check(await number(token, calldata('balanceOf(address)', account)), 883n, 'account retains denomination minus fee and transfer')
  check(await number(token, calldata('balanceOf(address)', receiver)), 100n, 'native ERC-20 transfer payout')
  check(await number(token, calldata('balanceOf(address)', feeRecipient)), 17n, 'native withdrawal relayer fee')
  check(await number(pool, selector('lastFee()')), 17n, 'Solidity pool independently decodes fee')
  check((await call(pool, selector('lastRoot()'))), native.root, 'Solidity pool independently decodes root')
  check(await number(recorder, selector('count()')), 2n, 'two native ordered calls ran')
  check(await number(recorder, calldata('seen(uint256)', 0)), 11n, 'first native call order')
  check(await number(recorder, calldata('seen(uint256)', 1)), 22n, 'second native call order')
  await send(account, native.revertBatch, { success: false })
  check(await number(recorder, selector('count()')), 2n, 'actual account atomically rolls back earlier calls')
  await send(account, native.tailBatch, { from: outsider, success: false })
  check(await number(recorder, selector('count()')), 2n, 'actual account rejects non-owner execution')

  // Full public validatePaymasterUserOp and postOp on the actual paymaster.
  // The synthetic token is also WETH, so no oracle is involved in this scope.
  const paymaster = await deploy('TornadoPaymaster', addressWord(entryPoint) + addressWord(zero) + addressWord(token) + word(300))
  await send(paymaster, calldata('setInstance(address,bool)', pool, 1))
  await send(token, calldata('mint(address,uint256)', pool, 1000))
  const validate = (sender, gas = 100000, maxCost = 10) => encode('validateNative(address,address,bytes,uint256,uint256)',
    paymaster, sender, native.sponsorParameters, gas, maxCost)
  await send(entryPoint, validate(outsider), { success: false })
  check(await number(token, calldata('balanceOf(address)', pool)), 1000n, 'recipient mismatch leaves pool funds untouched')
  await send(entryPoint, validate(account, 100000, 18), { success: false })
  check(await number(token, calldata('balanceOf(address)', pool)), 1000n, 'insufficient fee atomically rolls withdrawal back')
  await send(entryPoint, validate(account))
  check(await number(token, calldata('balanceOf(address)', paymaster)), 17n, 'actual paymaster receives exact native sponsor fee')
  check(await number(token, calldata('balanceOf(address)', account)), 1866n, 'actual paymaster uses native sponsor recipient')
  check((await call(pool, selector('lastRelayer()'))).slice(-40).toLowerCase(), clean(paymaster).toLowerCase(), 'actual paymaster forces itself as pool relayer')
  await send(entryPoint, calldata('postNative(address,uint256)', paymaster, 5))
  check(await number(token, calldata('balanceOf(address)', paymaster)), 5n, 'actual postOp retains actual test cost')
  check(await number(token, calldata('balanceOf(address)', account)), 1878n, 'actual postOp returns unused sponsor fee')

  // Actual public builder: one sponsor proof plus two reviewed tail calls.
  // Install real proxy/account and paymaster code at the fixture's fixed
  // addresses. Address identity and deployment are explicitly synthetic here.
  const builder = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tests/evm/Export.lean',
    '--builder', owner, recorder], { cwd: repository, encoding: 'utf8' }))
  const implementationSlot = '0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc'
  const implementationValue = await rpc('eth_getStorageAt', [account, implementationSlot, 'latest'])
  await rpc('anvil_setCode', [builder.account, await rpc('eth_getCode', [account, 'latest'])])
  await rpc('anvil_setStorageAt', [builder.account, implementationSlot, implementationValue])
  await send(builder.account, calldata('initialize(address)', owner))
  check((await call(builder.account, selector('owner()'))).slice(-40).toLowerCase(), clean(owner).toLowerCase(), 'etched actual account initializes using actual code')
  await rpc('anvil_setCode', [builder.paymaster, await rpc('eth_getCode', [paymaster, 'latest'])])
  // Ownable's slot is copied from its real constructor; immutable EntryPoint,
  // oracle factory, and WETH values are already patched in the actual runtime.
  await rpc('anvil_setStorageAt', [builder.paymaster, '0x' + word(0),
    await rpc('eth_getStorageAt', [paymaster, '0x0', 'latest'])])
  const ethPool = await deploy('ProbeEthPool', addressWord(verifier) + clean(builder.root))
  await rpc('anvil_setCode', [builder.pool, await rpc('eth_getCode', [ethPool, 'latest'])])
  await rpc('anvil_setBalance', [builder.pool, '0x' + BigInt(builder.denomination).toString(16)])
  await send(builder.paymaster, calldata('setInstance(address,bool)', builder.pool, 1))
  const sponsorCall = encode('validateNative(address,address,bytes,uint256,uint256)',
    builder.paymaster, builder.account, builder.paymasterData, 100000, 1)
  await send(entryPoint, sponsorCall)
  check(BigInt(await rpc('eth_getBalance', [builder.account, 'latest'])), BigInt(builder.denomination) - 1n,
    'actual builder and actual paymaster deliver reviewed ETH net payout')
  check(BigInt(await rpc('eth_getBalance', [builder.paymaster, 'latest'])), 1n,
    'actual builder sponsor pays exact proof-bound fee')
  await send(builder.account, builder.callData)
  check(await number(recorder, selector('count()')), 4n, 'actual builder two-call suffix executes')
  check(await number(recorder, calldata('seen(uint256)', 2)), 101n, 'actual builder first tail call')
  check(await number(recorder, calldata('seen(uint256)', 3)), 202n, 'actual builder second tail call')
  await rpc('anvil_setBalance', [builder.pool, '0x' + BigInt(builder.denomination).toString(16)])
  await send(entryPoint, sponsorCall, { success: false })
  check(BigInt(await rpc('eth_getBalance', [builder.account, 'latest'])), BigInt(builder.denomination) - 1n,
    'synthetic ledger rejects duplicate public nullifier without another payout')

  // Checked native deposit plans and backup reduction through the exact
  // pinned Simple7702 runtime. Code placement and the EntryPoint caller are
  // synthetic; no EIP-7702 authorization or complete handleOps is claimed.
  const delegatedRuntime = json('fixtures/simple7702-code.json')
  check(execFileSync('cast', ['keccak', delegatedRuntime.code], commandOptions).trim(),
    delegatedRuntime.codeHash, 'pinned Simple7702 runtime hash')
  const depositEntryPoint = '0x4337084d9e255ff0702461cf8895ce9e3b5ff108'
  await rpc('anvil_impersonateAccount', [depositEntryPoint])
  await rpc('anvil_setBalance', [depositEntryPoint, '0x' + (100n * 10n ** 18n).toString(16)])
  const seededGroups = json('fixtures/seeded-note-vectors.json').groups
  const depositTopic = execFileSync('cast', ['keccak', 'Deposit(bytes32,uint32,uint256)'], commandOptions).trim()
  const approvalTopic = execFileSync('cast', ['keccak', 'Approval(address,address,uint256)'], commandOptions).trim()
  for (const [caseName, depositSender] of [
    ['eth-backup', '0x2000000000000000000000000000000000000001'],
    ['token-split', '0x2000000000000000000000000000000000000002'],
  ]) {
    const deposit = JSON.parse(execFileSync('lake', ['env', 'lean', '--run', 'tests/evm/ExportDeposit.lean',
      caseName, depositSender], { cwd: repository, encoding: 'utf8' }))
    check(deposit.implementationHash, delegatedRuntime.codeHash, 'native runtime policy matches installed code')
    const expectedNotes = caseName === 'eth-backup' ? seededGroups[0].notes :
      [...seededGroups[0].notes, ...seededGroups[2].notes]
    const independentItems = expectedNotes.map(note => ({
      pool: caseName === 'eth-backup' ? note.pool : seededGroups[2].notes[0].pool,
      denomination: caseName === 'eth-backup' ? (() => {
        const [whole, fraction = ''] = note.denomination.split('.')
        return BigInt(whole) * 10n ** 18n + BigInt(fraction.padEnd(18, '0'))
      })() : 100000000n,
      commitment: note.commitment,
      token: caseName === 'eth-backup' ? null : '0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48',
    }))
    assert.deepEqual(deposit.items.map(item => item.commitment.toLowerCase()),
      expectedNotes.map(note => note.commitment.toLowerCase()), 'native backup reduction preserves independent public commitments')
    assertions++
    assert.deepEqual(deposit.items.map(item => ({ pool: item.pool.toLowerCase(),
      denomination: BigInt(item.denomination), token: item.token?.toLowerCase() ?? null })),
      independentItems.map(({ pool, denomination, token }) => ({ pool: pool.toLowerCase(), denomination, token })),
      'native backup/catalog projection agrees with independent original pools, amounts and token')
    assertions++
    check(deposit.plan.mode, 'simple7702', 'actual planner selects the initial undelegated batch route')
    check(deposit.plan.noteCount, expectedNotes.length, 'actual planner retains every backup note')
    check(BigInt(deposit.plan.amount), independentItems.reduce((sum, item) => sum + item.denomination, 0n), 'native plan amount equals the independent backup total')
    await rpc('anvil_setCode', [depositSender, delegatedRuntime.code])
    await rpc('anvil_setBalance', [depositSender, '0x' + (10n * 10n ** 18n).toString(16)])
    const uniquePools = [...new Map(deposit.items.map(item => [item.pool.toLowerCase(), item])).values()]
    let depositToken = zero
    if (caseName === 'token-split') {
      const localToken = await deploy('ProbeDepositToken')
      depositToken = deposit.items[0].token
      await rpc('anvil_setCode', [depositToken, await rpc('eth_getCode', [localToken, 'latest'])])
      await send(depositToken, calldata('mint(address,uint256)', depositSender, deposit.plan.amount))
    }
    for (const item of uniquePools) {
      const localPool = await deploy('ProbeDepositPool', addressWord(depositToken) + word(item.denomination))
      await rpc('anvil_setCode', [item.pool, await rpc('eth_getCode', [localPool, 'latest'])])
      await rpc('anvil_setBalance', [item.pool, '0x0'])
      if (caseName === 'token-split')
        await send(depositToken, calldata('seedAllowance(address,address,uint256)', depositSender, item.pool, 1))
    }
    const steps = deposit.plan.batches[0]
    const expectedFirstNotes = caseName === 'token-split' ? independentItems.slice(0, 4) : independentItems
    const expectedFirstAmount = expectedFirstNotes.reduce((sum, item) => sum + BigInt(item.denomination), 0n)
    check(steps.filter(step => step.kind === 'deposit').length, expectedFirstNotes.length, 'native first chunk has exact note count')
    const executed = await send(depositSender, deposit.plan.firstBatchData, { from: depositEntryPoint })
    const depositLogs = executed.logs.filter(log => log.topics[0] === depositTopic)
    assert.deepEqual(depositLogs.map(log => log.topics[1].toLowerCase()),
      expectedFirstNotes.map(item => item.commitment.toLowerCase()), 'Solidity decodes exact backup commitments in their order')
    assertions++
    assert.deepEqual(depositLogs.map(log => log.address.toLowerCase()),
      expectedFirstNotes.map(item => item.pool.toLowerCase()), 'native deposit calls use exact original catalog pools')
    assertions++
    for (const item of uniquePools) {
      const expectedAtPool = expectedFirstNotes.filter(note => note.pool.toLowerCase() === item.pool.toLowerCase())
      check(await number(item.pool, selector('count()')), BigInt(expectedAtPool.length), 'synthetic ledger records exact per-pool count')
      for (let index = 0; index < expectedAtPool.length; index++)
        check((await call(item.pool, calldata('commitments(uint256)', index))).toLowerCase(),
          expectedAtPool[index].commitment.toLowerCase(), 'synthetic ledger independently stores native bytes32')
    }
    if (caseName === 'eth-backup') {
      check(BigInt(await rpc('eth_getBalance', [depositSender, 'latest'])), 10n * 10n ** 18n - expectedFirstAmount,
        'ETH native plan spends exact independently summed denominations')
      for (const item of uniquePools) {
        const count = expectedFirstNotes.filter(note => note.pool.toLowerCase() === item.pool.toLowerCase()).length
        check(BigInt(await rpc('eth_getBalance', [item.pool, 'latest'])), BigInt(item.denomination) * BigInt(count), 'ETH pool receives exact deposit values')
      }
    } else {
      check(deposit.insufficientTokenRejected, true, 'actual certified planner rejects a deficient token snapshot')
      assert.deepEqual(steps.slice(0, 2).map(step => step.kind), ['reset', 'approve'], 'native plan resets before exact allowance')
      assertions++
      check(BigInt(steps[1].approvalAmount), expectedFirstAmount, 'native first batch approves exactly four notes, not all six')
      check(deposit.plan.batches[1].length, 2, 'native split avoids a singleton final batch')
      assert.deepEqual(executed.logs.filter(log => log.address.toLowerCase() === depositToken.toLowerCase() &&
        log.topics[0] === approvalTopic).map(log => BigInt(log.data)), [0n, expectedFirstAmount], 'Solidity observes reset then exact approval')
      assertions++
      check(await number(depositToken, calldata('allowance(address,address)', depositSender, uniquePools[0].pool)), 0n, 'first native batch consumes exactly its allowance')
      check(await number(depositToken, calldata('balanceOf(address)', uniquePools[0].pool)), expectedFirstAmount, 'token pool receives exact first-chunk denomination sum')
      check(await number(depositToken, calldata('balanceOf(address)', depositSender)), BigInt(deposit.plan.amount) - expectedFirstAmount, 'unexecuted second chunk funds stay with sender')
      check(BigInt(await rpc('eth_getBalance', [uniquePools[0].pool, 'latest'])), 0n, 'native token deposit values are zero ETH')
      check(deposit.sufficientAllowancePlan.batches[0].every(step => step.kind === 'deposit'), true, 'actual planner omits approval when allowance is sufficient')
      check(deposit.replanned.batches[0][0].kind, 'approve', 'later forced replan freshly approves remaining notes')
      const later = await send(depositSender, deposit.replanned.firstBatchData, { from: depositEntryPoint })
      const laterLogs = later.logs.filter(log => log.topics[0] === depositTopic)
      assert.deepEqual(laterLogs.map(log => log.topics[1].toLowerCase()),
        deposit.items.slice(4).map(item => item.commitment.toLowerCase()), 'fresh native replan deposits only the exact remaining suffix')
      assertions++
      check(await number(uniquePools[0].pool, selector('count()')), 6n, 'all six public synthetic note commitments were deposited once')
      check(await number(depositToken, calldata('balanceOf(address)', depositSender)), 0n, 'fresh replan consumes remaining token budget')
      check(await number(depositToken, calldata('allowance(address,address)', depositSender, uniquePools[0].pool)), 0n, 'fresh replan leaves no excess allowance')
    }
  }

  console.log(`PASS: ${assertions} local EVM assertions; 3 real Classic proofs + 18 changed-public-signal rejections; actual withdrawal/deposit builders, SimpleAccount/factory, pinned Simple7702 runtime and TornadoPaymaster; synthetic EntryPoint/token/pool/address placement.`)
} finally {
  if (anvil && anvil.exitCode === null) {
    anvil.kill('SIGTERM')
    await Promise.race([new Promise(resolve => anvil.once('exit', resolve)), delay(3000)])
    if (anvil.exitCode === null) anvil.kill('SIGKILL')
  }
  built.cleanup()
}
