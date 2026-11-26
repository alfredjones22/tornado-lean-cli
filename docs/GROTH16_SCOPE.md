# Tornado Groth16 scope

The native CLI implements the complete pinned Withdraw(20) proving route:
31-byte nullifier and 31-byte secret, a 20-level MiMC path, six public signals,
complete witness generation, sparse-key H calculation, BN254 point assembly,
256-byte Solidity serialization, and compiled-key verification. Independent
fixtures use pinned `@kohaku-eth/tornado-cash@0.1.0-alpha.40` and
`micro-zk-proofs@0.3.1` reference implementations; source identities and hashes
remain recorded in the fixtures and their generators.
The runnable arithmetic is native Lean, variable time and nonzeroizing.

## What the kernel proofs establish

The [mathematical workspace](../proofs/README.md) certifies the actual field
primes and extension towers, both curve groups, native scalar/MSM loops and
normalization, full FFT/IFFT and H/QAP construction, complete A/B/C assembly,
and exact eight-word encoding. Native reduced Tate bilinearity is derived
from curve functions and the actual Miller program. A closed public arithmetic
trace certifies its generator result is nontrivial. The original verifier's
scalar-equation equivalence and conditional completeness are proved on the
specified generator spans and finite-point domain.

The [application workspace](../app-proofs/README.md) connects actual primitive
execution, all ordered signal phases, complete witness materialization and
every R1CS row to explicit original-input source conditions. Its public gate
regenerates local equations and checks their elimination against every pinned
constraint, binds native generator/subgroup receipts to the circuit bases,
and validates the complete independent point schedule before reading a note
or entropy. The untrusted extractor and its JSON supply no mathematical axioms.
See [witness scope](WITNESS_VM_SCOPE.md).

The remaining Pedersen refinement is discharged in
`ReferenceProgramMeaning.referenceMeaning_construct`: exact original note
bytes, all five signed-window segments, actual curve operations and the
native hash coordinates agree. `InputInverse.prepareInputPrefix_iff_source`
proves that those independent source conditions characterize the original
input validator's successful results. Final witness or R1CS acceptance is
not a source premise.

The actual worker's proof output and failures factor through the ideal
Groth16 triple. Under the documented source, setup and IID-byte hypotheses,
its terminal distribution is within `2^-251` of an explicit witness-free
reference distribution. The reference uses abstract setup trapdoor scalars;
it is not an efficient public simulator or trapdoor-recovery program.
See [blinding/output scope](PROOF_BLINDING_SCOPE.md).

## Finite independent evidence

Public fixtures check all 28,300 witness values against the pinned SDK and
all 28,275 original constraints. Additional cases exercise different notes and
a rightmost 20-level Merkle path. A complete public proof with fixed test
blinding `r=1,s=2` matches all 256 SDK bytes and passes both native verification
and an independent optimal-Ate check; every one-unit public-signal mutation
is rejected. Other vectors cover arithmetic, roots, MSMs, a separate square
circuit, malformed points, non-subgroup G2 points, canonical encodings and
structural certificate mutations. These examples complement universal
statements; they are not cryptographic security proofs.

The pinned circuit's raw SHA-256 is
`3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98`;
the key's is `8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af`.
Hashes authenticate bytes, not setup honesty or deployed code.

## Explicit boundaries

- Setup/query/key relations, polynomial row alignment and degree bounds are
  mathematical hypotheses, not consequences of a digest. Public artifact
  comparisons provide additional finite evidence; the entire binary parser
  and setup ceremony are not kernel-certified.
- Native Tate is not formally identified with the implementation of
  Ethereum's optimal-Ate precompile. Native verifier scalar equivalence is
  algebraic correctness, not Groth16 knowledge soundness or cryptographic
  hardness. The selected pool's deployed verifier remains an external boundary.
- The executable rejects affine A/B/C or the public-input commitment at
  infinity. Completeness states those finite-point conditions explicitly.
  Privacy includes the resulting failures and does not guarantee a positive
  release probability by itself; completeness is a separate result.
- File/process/network effects, physical entropy, compiler/runtime behavior,
  time, resources, crashes and secret erasure remain assumptions or outside
  scope. The output theorem does not cover arbitrary malformed note parsing
  or signing/metadata modes' cryptographic contents.
- RPC root membership and unspentness do not authenticate Ethereum consensus.
  The review/journal/exposure/receipt rules have their own selected source
  proofs and fault tests; R1CS satisfaction alone establishes none of them.

Verification uses public, unfunded fixtures and synthetic local EVM state.
No real or funded transaction is part of the gate. See the
[security specification](WITHDRAWAL_SECURITY_SPEC.md),
[verification instructions](VERIFICATION.md) and [pipeline scope](CLASSIC_PROOF_PIPELINE_SCOPE.md).
