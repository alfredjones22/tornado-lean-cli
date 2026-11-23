# Native typed transaction boundary

[`TypedTransaction.lean`](../Tornado/Protocol/TypedTransaction.lean) is pure Lean code for
the CLI's EIP-1559 EOA signing route and for EIP-7702 authorization signatures
and type-4 authorization-list transaction envelopes. It uses the native RLP,
Keccak, and deterministic secp256k1 modules; the runtime does not call viem.
[`TypedTransactionDecode.lean`](../Tornado/Protocol/TypedTransactionDecode.lean)
strictly parses type-2 and type-4 envelopes. It rejects nonminimal RLP lengths,
leading-zero integers, malformed nested access/authorization lists, extra
fields, and trailing bytes. An accepted result carries a Lean proof that
re-encoding its decoded fields produces the exact original byte array.

The [fixture](../fixtures/typed-transactions.json) was generated from the pinned
`tornado-cli-new-era` dependency `viem@2.55.19` with a public test key of scalar
one. [`TypedTransaction.lean` tests](../tests/TypedTransaction.lean) compare four
type-4 transaction shapes, their unsigned signing hashes, simple-signed bytes
and hashes, and native-signed bytes and hashes; one native-signed EIP-1559
transaction; and three native EIP-7702 authorization signatures. It also
decodes unsigned and signed type-2/type-4 viem vectors and exercises malformed
or noncanonical RLP. The suite passes 43 compatibility checks and 22
malformed-field rejections.

Eight kernel-checked encoder theorems establish that the native authorization encoding
preserves the list count; the type-4 unsigned field list contains the complete
authorization list in its tenth slot; successful type-4 serialization requires
the entire authorization list to pass validation; zero transaction chain IDs and invalid
delegate widths are rejected; a signed authorization retains the supplied
chain, delegate and nonce and passed native validation; and successful native
signing returns a hash of exactly the returned serialized bytes for both typed
transaction variants. Two further decoder theorems expose the exact
re-encoding proofs carried by accepted type-2 and type-4 results. These are
properties of the Lean implementation. The
finite viem vectors support compatibility for selected cases, not all-input
equivalence or ECDSA security.

The pinned TypeScript CLI uses EIP-1559 transactions for sequential deposits
and smart-account recovery. Its EIP-7702 authorization is currently carried in
an ERC-4337 UserOperation rather than a type-4 EOA transaction; type-4 support
here is a dependency-completeness step and is not a claim of current command
parity. In either route, a caller must independently obtain and verify chain
ID, pending nonce, gas and fee values, address ownership, delegation target,
and call data; durably reserve the signed hash before exposing the operation;
and reconcile an ambiguous send by the exact chain receipt and events. None
of those effectful steps are in this module.

The native secp256k1 arithmetic is variable-time and does not zeroize private
keys. The public test key is never a live wallet key. Connected owner-key send
routes use protected native libsecp256k1 signing and Lean serialization instead
of importing their key into these reference signing functions. Direct
note-derived signing occurs inside the experimental Lean worker and retains
the variable-time/nonzeroizing limitation. Viem accepts an empty authorization list as a
serialization input; the native encoder matches that behavior, while actual
chain acceptance is outside this module's proof scope. The strict decoder
accepts only signatures whose scalars are below the secp256k1 order and limits
each RLP child list to 4,096 entries; those are deliberate resource and
canonicality bounds, so it is not a generic all-input RLP parser.
