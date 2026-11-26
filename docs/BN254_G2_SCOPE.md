# Native BN254 G2 arithmetic scope

[`BN254G2.lean`](../Tornado/Protocol/BN254G2.lean) implements the quadratic extension field `Fp2` and BN254 twist G2 Jacobian add, double, scalar multiplication, and affine normalization in native Lean. It shares the bounded base-field values from [`BN254G1.lean`](../Tornado/Protocol/BN254G1.lean). Unlike the G1 helper, G2 scalar multiplication does not reduce its scalar modulo the subgroup order, so an order check is meaningful.

[`tests/BN254G2.lean`](../tests/BN254G2.lean) checks 14 public scalar/addition outputs against [pinned noble vectors](../fixtures/bn254-g2-vectors.json), verifies the pinned generator has the expected scalar order, and rejects off-twist, out-of-field, and zero-inverse inputs. [`generate-bn254-g2-vectors.mjs`](../scripts/generate-bn254-g2-vectors.mjs) regenerates those vectors from the pinned independent noble dependency; `--check` compares them byte for byte. These finite checks do not prove the full group law, subgroup membership of arbitrary decoded points, or equivalence for all inputs.

The [mathematical workspace](../proofs/README.md) additionally proves Fp2
field interpretation and inverse construction, all admitted native G2
add/double branches, total scalar multiplication, normalization, windowed MSM
and exact generator order. Native operations map to Mathlib's elliptic-curve
group; equality of normalized observations is derived from that group meaning.
These are universal source-level results, beyond the finite vectors.

Arbitrary decoded on-twist points are not automatically in the prime subgroup.
The public pairing checks subgroup membership; honest query/key spans are
explicit hypotheses in the assembly/verifier results. Field/group correctness
does not establish setup honesty, discrete-log hardness or a deployed verifier.

This module supplies the native prover and public pairing. Its bigint
operations are variable time and do not zeroize secrets. Verification uses
public unfunded fixtures; experimental commands have no production
side-channel or secret-erasure guarantee.
