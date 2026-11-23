// Development-only viem oracle. Every value is a public, unfunded fixture.
import { createRequire } from 'node:module'
import { writeFileSync } from 'node:fs'
const require = createRequire(new URL('../../tornado-cli-new-era/package.json', import.meta.url))
const { encodeFunctionData, encodeAbiParameters, encodeEventTopics, parseAbi, toHex } = require('viem')
const { getUserOperationHash } = require('viem/account-abstraction')
const entryPoint = '0x4337084d9e255ff0702461cf8895ce9e3b5ff108'
const sender = '0x0000000000000000000000000000000000000001'
const recipient = '0x0000000000000000000000000000000000000002'
const paymaster = '0xb0ffcdc890e969579d348f519a9c3920c2dd04a5'
const pool = '0x199112eb461ea7eec1d75b33343542e1d069b41c'
const beneficiary = '0x000000000000000000000000000000000000dead'
const op = { sender, nonce: 0n, callData: '0x1234', verificationGasLimit: 50000n,
  callGasLimit: 100000n, preVerificationGas: 100000n, maxFeePerGas: 1000000000n,
  maxPriorityFeePerGas: 100000000n, paymaster, paymasterVerificationGasLimit: 450000n,
  paymasterPostOpGasLimit: 50000n, paymasterData: '0x1234', signature: '0x' + '11'.repeat(64) + '1b' }
const pair = (high, low) => toHex(high, { size: 16 }) + toHex(low, { size: 16 }).slice(2)
const packed = { sender, nonce: op.nonce, initCode: '0x', callData: op.callData,
  accountGasLimits: pair(op.verificationGasLimit, op.callGasLimit), preVerificationGas: op.preVerificationGas,
  gasFees: pair(op.maxPriorityFeePerGas, op.maxFeePerGas),
  paymasterAndData: paymaster + pair(op.paymasterVerificationGasLimit, op.paymasterPostOpGasLimit).slice(2) + op.paymasterData.slice(2),
  signature: op.signature }
const abi = parseAbi(['function handleOps((address sender,uint256 nonce,bytes initCode,bytes callData,bytes32 accountGasLimits,uint256 preVerificationGas,bytes32 gasFees,bytes paymasterAndData,bytes signature)[] ops,address beneficiary)',
  'event UserOperationEvent(bytes32 indexed userOpHash,address indexed sender,address indexed paymaster,uint256 nonce,bool success,uint256 actualGasCost,uint256 actualGasUsed)',
  'event Withdrawal(address to,bytes32 nullifierHash,address indexed relayer,uint256 fee)'])
const hash = getUserOperationHash({ userOperation: op, entryPointAddress: entryPoint, entryPointVersion: '0.8', chainId: 1 })
const nullifier = toHex(7n, { size: 32 })
const logs = [{ address: entryPoint,
  topics: encodeEventTopics({ abi, eventName: 'UserOperationEvent', args: { userOpHash: hash, sender, paymaster } }),
  data: encodeAbiParameters([{ type: 'uint256' }, { type: 'bool' }, { type: 'uint256' }, { type: 'uint256' }], [0n, true, 1n, 1n]) },
{ address: pool, topics: encodeEventTopics({ abi, eventName: 'Withdrawal', args: { relayer: paymaster } }),
  data: encodeAbiParameters([{ type: 'address' }, { type: 'bytes32' }, { type: 'uint256' }], [recipient, nullifier, 1n]) }]
const result = { viemVersion: require('viem/package.json').version, hash,
  handleOpsData: encodeFunctionData({ abi, functionName: 'handleOps', args: [[packed], beneficiary] }),
  response: [{ number: '0x64', calls: [{ status: '0x1', gasUsed: '0x1', logs }] }] }
writeFileSync(new URL('../fixtures/entrypoint-simulation.json', import.meta.url), JSON.stringify(result, null, 2) + '\n')
