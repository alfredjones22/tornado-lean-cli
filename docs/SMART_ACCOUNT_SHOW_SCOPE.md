# Smart-account show scope

Tornado.Cli.SmartAccountShow.showCommand implements the read-only
smart-account show --owner <address> [--chain <id>] [--rpc <url>] command.
It follows the pinned TypeScript command's defaults and output order: owner,
deterministic smart-account address, deployment state, EntryPoint nonce,
supported-asset balances in catalog order, and EntryPoint deposit. Chain 1 is
the default. --rpc, TORNADO_RPC_URL, and then the pinned catalog's default
RPC are considered in that order. The native transport accepts HTTPS and
explicit loopback HTTP endpoints for local development.

The command uses the existing pure SimpleAccount recovery constants and ABI
builders, catalog, EIP-55 checksum logic, typed JSON-RPC envelope, and HTTPS
transport. It checks the selected chain ID, pins all state reads to one
canonical block number, checks the v0.8 factory and implementation bytecode
hashes, rejects contract-wallet owners other than EIP-7702 delegation markers,
checks the implementation EntryPoint, and checks owner, EntryPoint, and ERC-1967
implementation slot for deployed accounts. For an undeployed account it still
reads the EntryPoint nonce and supported balances.

The destination is independently calculated with CREATE2 from the pinned
factory, exact proxy creation bytecode, implementation, owner and withdrawal
salt. A fabricated `getAddress` reply cannot select another destination even
if the same RPC also invents owner, code and storage replies. The public
fixture reconstructs the existing factory and implementation code hashes
from v0.8 deployment artifacts and compares six address predictions with
viem. This reduces RPC trust for destination selection; it does not prove
chain state, deployment or finality.

The ABI decoders require exact 32-byte words and reject nonzero address
padding. Quantities use the canonical uint256 parser. The output only includes
assets from the pinned catalog for the selected chain. The offline test
tests/SmartAccountShow.lean checks public RPC-shaped responses, viem-derived
factory calldata, EIP-55 acceptance, malformed data rejection, catalog order,
formatting, and input rejection before network access.

These checks establish consistency of data returned by the chosen RPC. They do
not authenticate the RPC against chain consensus or prove that the account is
deployed on the canonical chain. Reads use one block number, but a reorg at
that height can still mix states between calls; block-hash pinning or a trusted
snapshot is needed to rule that out. The block number does not prove finality.
No private keys, protected
note backups, proof material, signed operations, transactions, or bundler calls
enter this path. A funded live-chain run has not been performed.
