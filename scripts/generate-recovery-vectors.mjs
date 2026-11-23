// Development oracle for pure Lean recovery-call parity. No RPC is called.
import { writeFileSync } from 'node:fs'
import { encodeFunctionData, erc20Abi, toHex } from '/Users/x/dev/personal/tornado-cli-new-era/node_modules/viem/_esm/index.js'
import { assetsFor } from '/Users/x/dev/personal/tornado-cli-new-era/src/domain/catalog.ts'
import { accountFactoryData, simpleAccountAbi, WITHDRAWAL_ACCOUNT_SALT } from '/Users/x/dev/personal/tornado-cli-new-era/src/smart-account/account.ts'

const owner = '0x1111111111111111111111111111111111111111'
const account = '0x2222222222222222222222222222222222222222'
const recipient = '0x3333333333333333333333333333333333333333'
const cases = [
  { name: 'mainnet-mixed-balances', chainId: 1,
    balances: [1000000000000000n, 1000000000000000000n, 1234567n, 0n, 1n],
    entryPointDeposit: 100000000000000n },
  { name: 'sepolia-entrypoint-only', chainId: 11155111,
    balances: [0n, 0n], entryPointDeposit: 123n },
  { name: 'mainnet-eth-only', chainId: 1,
    balances: [500000000000000000n, 0n, 0n, 0n, 0n], entryPointDeposit: 0n },
]

const output = []
for (const row of cases) {
  const assets = assetsFor(row.chainId)
  if (assets.length !== row.balances.length) throw new Error('Catalog drift')
  const calls = assets.flatMap((asset, index) => {
    const amount = row.balances[index]
    if (amount === 0n) return []
    return [asset.token ? {
      target: asset.token, value: 0n,
      data: encodeFunctionData({ abi: erc20Abi, functionName: 'transfer', args: [recipient, amount] }),
    } : { target: recipient, value: amount, data: '0x' }]
  })
  if (row.entryPointDeposit > 0n) calls.push({
    target: account, value: 0n,
    data: encodeFunctionData({ abi: simpleAccountAbi, functionName: 'withdrawDepositTo',
      args: [recipient, row.entryPointDeposit] }),
  })
  output.push({
    name: row.name, chainId: row.chainId, owner, account, recipient,
    balances: row.balances.map(String), entryPointDeposit: String(row.entryPointDeposit),
    factorySalt: toHex(WITHDRAWAL_ACCOUNT_SALT, { size: 32 }),
    factoryData: accountFactoryData({ owner, salt: WITHDRAWAL_ACCOUNT_SALT }),
    calls: calls.map(call => ({ to: call.target, value: String(call.value), data: call.data })),
    data: encodeFunctionData({ abi: simpleAccountAbi, functionName: 'executeBatch', args: [calls] }),
  })
}
writeFileSync(new URL('../fixtures/recovery-vectors.json', import.meta.url),
  JSON.stringify({ vectors: output }, null, 2) + '\n')
console.log(`Generated ${output.length} native recovery-call vectors.`)
