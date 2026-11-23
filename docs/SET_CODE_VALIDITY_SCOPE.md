# EIP-7702 stateless validity and intent gate

[`SetCodeValidity.lean`](../Tornado/Protocol/SetCodeValidity.lean) adds a strict,
pure admission gate above the existing viem-compatible type-4 serializer. It
does not change the raw serializer or decoder. This distinction matters:
viem can serialize an empty authorization list, a null destination, or a
high-S signature even though those bytes do not satisfy the intended
protocol or wallet behavior.

The `validateSetCodeEnvelope` entry point requires a signed transaction with:

- a nonnull destination and at least one authorization;
- every authorization nonce below `2^64`, as required for transaction validity;
- enough gas for the EIP-2930 base, calldata, and access-list costs plus
  `25,000` gas per authorization;
- low-S outer signature and the existing raw base, field-width, fee-ordering,
  access-list, and signature-scalar checks.

The stricter `validateSetCodeIntent` additionally requires **every**
authorization to pass the *stateless* checks that precede application: its
chain ID must be the outer chain ID or wildcard zero; its nonce must be below
`2^64 - 1`; and its signature must be low-S. Per
[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702), a tuple that fails one of
these processing checks is skipped while the outer transaction can remain
valid. A caller expecting a delegation should therefore use the intent gate,
not infer that broadcast or inclusion implies that all authorizations took
effect. The all-zero delegate remains valid for revocation.

`serializeSetCodeIntent` runs the intent gate and then calls the unchanged
`serialize7702` function. Nine kernel-checked theorems establish that an
accepted envelope has a destination and nonempty list, covers calculated
intrinsic gas, has a low-S outer signature, and bounds every authorization
nonce; an accepted intent passes the per-tuple stateless predicate and its
nonce limit; and strict serialization returns exactly the raw serializer's
bytes. `#print axioms` reports only Lean's standard `propext` and `Quot.sound`.

[`SetCodeValidity.lean` tests](../tests/SetCodeValidity.lean) run 34 focused
checks, including each side of the `2^64` nonce boundary, high-S and low-S
boundary signatures, a chain mismatch, zero-delegate revocation, minimum gas
and calldata/access-list gas arithmetic, raw-vs-strict behavior, and a native
signature generated with the public scalar-one test key. Run:

```sh
lake build Tornado.Protocol.SetCodeValidity
lake env lean --run tests/SetCodeValidity.lean
```

This is a **one-way, conservative stateless gate**, not a full consensus
implementation. The existing raw validation rejects some tuple encodings
that a consensus client could admit and then skip, such as parity above one;
thus acceptance supports the stated properties, while rejection does not
prove that a transaction is consensus-invalid. The gate does not recover
signature authorities, establish which account signed, read an account's
current nonce or code, establish delegate code identity, verify the chain's
base fee or block gas limit, or prove that a transaction was included and
finalized. Those require native recovery and a trusted, fresh chain-state
boundary. It also does not harden variable-time native secp256k1 arithmetic
for live secrets. The experimental CLI's ERC-4337 authorization routes use
their own validation; this type-4 envelope gate is a separate library API.
