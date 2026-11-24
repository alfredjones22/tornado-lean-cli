# Local EVM interoperability scope

Run from the repository root:

```sh
node scripts/test-local-evm.mjs
```

The runner compiles pinned sources offline, checks their source/compiler/bytecode
hashes against `fixtures/evm/artifact-provenance.json`, starts its own fresh Anvil
on `127.0.0.1` with an ephemeral port and chain ID 31337, runs synthetic
transactions, and stops Anvil and removes compiler output in `finally`.
It accepts no RPC URL, fork URL, private key, or signing/broadcast option.

Prerequisites are Node 20+, the repository's Lean toolchain and compiled imports,
`forge`, `cast`, `anvil`, and cached solc 0.7.6 and 0.8.28. The tested Foundry
installation is v1.6.0 nightly. Compilation uses `forge build --offline`.
The actual account/paymaster sources must be available in the sibling checkout
`../kohaku-contracts/privacy-paymaster`, or in the local directory named by
`TORNADO_EVM_CONTRACTS_SOURCE`.

The source checkout and submodule revisions are checked before compilation:

- Privacy paymaster: `1b23e91a06fb4af50220507febf38bd05078e6a4`.
- Account abstraction: `4cbc06072cdc19fd60f285c5997f4f7f57a588de`.
- OpenZeppelin: `5fd1781b1454fd1ef8e722282f86f9293cacf256`.

The completed extended suite passes 133 local EVM assertions. This includes
the 73-assertion withdrawal baseline, with three accepted public proofs and
eighteen rejected single-public-signal mutations, plus the deposit cases below.

Every transitive Solidity source has a SHA-256 entry in the provenance fixture.
The fixture also pins the compiler version, optimizer settings, EVM target,
metadata hash setting, creation bytecode hash, and runtime hash before constructor
immutables are patched. Classic Verifier uses solc 0.7.6 / Istanbul; the other
contracts use solc 0.8.28 / Cancun, both optimized with 200 runs and metadata
bytecode hash `none`. To deliberately regenerate these pins after reviewing a
source change, run `node scripts/build-local-evm-fixtures.mjs --pin`.

## Actual contracts and native output exercised

The unchanged vendored Classic Solidity `Verifier` executes the EIP-196/EIP-197
precompiles in Anvil. Three independently generated public Groth16 fixtures must
return true. For each fixture, changing any one of the six public signals must
return false: root, nullifier hash, recipient, relayer, fee, and refund. This is
an independent Solidity/EVM check of the proof encoding, G2 ordering, verifying
key, and public signal binding.

The actual `SimpleAccountFactory`, `ERC1967Proxy`, and `SimpleAccount` receive
native Lean `createAccount` and composed `executeBatch` calldata. The local
factory prediction is compared with the deployed account, and its actual owner
getter is checked. A native four-call batch withdraws synthetic tokens, sends
the exact fee, transfers the reviewed amount, and records two calls in order.
A failing middle call must roll back earlier state changes, and another local
sender must fail the account's owner authorization.

The actual `TornadoPaymaster.validatePaymasterUserOp` decodes the native sponsor
tuple and calls the synthetic token pool. Tests check exact recipient and fee,
its use of itself as relayer, rejection of a different recipient with execution
gas, and rollback on an insufficient fee. Its actual `postOp` refunds the unused
part of the fee using a controlled test cost. The synthetic token is configured
as WETH, exercising the paymaster's 1:1 fee path without a Uniswap oracle.

`tests/evm/Export.lean --builder` additionally derives the known public note and
its one-leaf MiMC path, loads the public account-profile proof, and calls the
actual `SponsoredWithdrawal.batch` builder. That builder verifies the proof and
passes its semantic acceptance gate. Its emitted sponsor tuple and ordered
two-call suffix then execute through the actual paymaster and account. The ETH
net payout equals the catalog denomination minus the proof-bound fee of one wei.
The synthetic ETH ledger calls the actual Solidity verifier and rejects another
withdrawal of the same public nullifier.

`tests/evm/ExportDeposit.lean` reads the existing public seeded backup through
the actual `DepositMulti.publicItems`, then calls the actual certified
`DepositMulti.preparePlan` and `DepositBatch7702.callsData`. An independent SDK
vector supplies expected commitments, catalog pool addresses, and denomination
amounts. Those original values are compared with the native public projection
before any synthetic ledger is configured. The emitted ETH calls must deposit
all four backup commitments in order with the exact independently summed value.

A second case builds six public synthetic 100-USDC notes by relabeling the
asset and denomination of the six already-public preimages in the seeded test
vectors. Their independently pinned commitments remain unchanged. It checks
the planner's four-plus-two split, reset-to-zero before approval, approval of
exactly the first four notes, token deposits carrying zero ETH, no excess
allowance, and retention of the second chunk's token budget. A fresh forced
replan supplies the remaining two deposits and their new exact approval. The
native planner must also omit approvals for sufficient allowance and reject a
deficient token snapshot. No spend proof is generated for these relabeled notes.

Deposit execution uses the exact runtime in `fixtures/simple7702-code.json`.
Its Keccak hash must equal both the fixture hash and the native CLI's pinned
implementation policy. This bytecode snapshot is executed directly; its source
compilation is not reproduced by the Solidity compiler-provenance step. Anvil
places this runtime at synthetic sender addresses and impersonates its fixed
EntryPoint caller. The synthetic token enforces reset-before-approve, and the
synthetic deposit ledger independently decodes commitments and requires exact
ETH or ERC-20 amounts.

## Deliberate synthetic boundaries

The EntryPoint, ERC-20s, token pools, deposit ledgers, recorder, revert target,
and single-root ETH ledger are test fixtures. The ETH ledger checks a fixed synthetic root and an
actual Groth16 proof; it does not implement the Classic Merkle tree or deposits.
The token pool does not verify proofs. No test claims that a real deployed
Classic pool recognizes these synthetic roots or contains a funded note.

The fixed account and pinned paymaster addresses used by the builder scenario
are populated with `anvil_setCode`. The proxy receives its implementation slot
from a genuinely created local proxy and runs the actual initializer. The
paymaster receives the ownership slot produced by its actual constructor; its
immutable fields remain those in its locally deployed runtime. This tests
execution of actual code at controlled addresses. It does not establish live
factory address identity, pinned deployment code hashes, or production storage.

Validation, execution, and `postOp` are called through an explicit synthetic
EntryPoint boundary. This suite does not run complete `handleOps`, validate
owner signatures, test EntryPoint gas charging or deposits, prove nonce/replay
handling, check bundler ERC-7562 behavior, verify an oracle, or use chain history.
Mainnet-shaped builder input is exercised on the isolated chain without signing;
cross-chain signature binding is outside this test.
The deposit runtime placement additionally bypasses EIP-7702 authorization and
delegation lifecycle checks; those are not established by successful execution
of its account methods.

The imported paymaster and base paymaster remain `SPDX-License-Identifier:
UNLICENSED`. They are compiled from the user's local pinned checkout into a
temporary directory. Their source and bytecode are not vendored into this
repository. The MIT notice on the synthetic harness applies to that harness's
own code and does not change the imported source licenses.
