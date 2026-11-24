import LeanCrypto.Groth16.MSM
import LeanCryptoProofs.G1GroupLaw

/-! Proof-only access to the exact private native implementation. These
elaborators emit its existing kernel constants; they add no axioms or runtime
replacement. The component helpers are definitionally tied below. -/
open Lean Elab Term Meta

elab "actualMsmWindowBits" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.MSM `LeanCrypto.Groth16.MSM.windowBits)
elab "actualMsmWindowed" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.MSM `LeanCrypto.Groth16.MSM.windowed)

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

abbrev bits (count : Nat) : Nat := actualMsmWindowBits count
def radix (count : Nat) : Nat := 2 ^ bits count
def windows (count : Nat) : Nat := (254 + bits count - 1) / bits count

abbrev nativeWindowed {α : Type} [Inhabited α] (points : Array α) (scalars : Array Nat)
    (zero : α) (add : α → α → α) (double : α → α) : α :=
  actualMsmWindowed points scalars zero add double

def fillBuckets {α : Type} [Inhabited α] (points : Array α) (scalars : Array Nat)
    (zero : α) (add : α → α → α) (divisor radix : Nat) : Array α := Id.run do
  let mut buckets := Array.replicate radix zero
  for i in [0:points.size] do
    let digit := scalars[i]! / divisor % radix
    if digit != 0 then
      buckets := buckets.set! digit (add buckets[digit]! points[i]!)
  return buckets

def collapseBuckets {α : Type} [Inhabited α] (buckets : Array α) (zero result : α)
    (add : α → α → α) (radix : Nat) : α := Id.run do
  let mut output := result
  let mut running := zero
  for d in [1:radix] do
    let digit := radix - d
    running := add running buckets[digit]!
    output := add output running
  return output

def windowedComponents {α : Type} [Inhabited α] (points : Array α) (scalars : Array Nat)
    (zero : α) (add : α → α → α) (double : α → α) : α := Id.run do
  let mut result := zero
  for w in [0:windows points.size] do
    for _ in [0:bits points.size] do result := double result
    let shift := (windows points.size - 1 - w) * bits points.size
    let divisor := 2 ^ shift
    let buckets := fillBuckets points scalars zero add divisor (radix points.size)
    result := collapseBuckets buckets zero result add (radix points.size)
  return result

theorem nativeWindowed_eq_components {α : Type} [Inhabited α]
    (points : Array α) (scalars : Array Nat) (zero : α)
    (add : α → α → α) (double : α → α) :
    nativeWindowed points scalars zero add double =
      windowedComponents points scalars zero add double := by
  rfl

theorem radix_capacity (count : Nat) : LeanCrypto.Groth16.MSM.order ≤ radix count ^ windows count := by
  unfold radix windows
  simp only [show bits count = (if count >= 2048 then 10 else if count >= 64 then 6 else 4) from rfl]
  split
  · decide +kernel
  · split <;> decide +kernel

theorem digit_sum_mod (scalar radix length : Nat) :
    (∑ index ∈ Finset.range length, radix ^ index * (scalar / radix ^ index % radix)) =
      scalar % radix ^ length := by
  induction length with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, pow_zero] using (Nat.mod_one scalar).symm
  | succ length ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

/-- The exact windowBits/windows choices retain every canonical scalar bit. -/
theorem native_digits_reconstruct (scalar count : Nat)
    (canonical : scalar < LeanCrypto.Groth16.MSM.order) :
    (∑ index ∈ Finset.range (windows count),
      2 ^ (index * bits count) * (scalar / 2 ^ (index * bits count) % radix count)) = scalar := by
  have bound := lt_of_lt_of_le canonical (radix_capacity count)
  have reconstructed := digit_sum_mod scalar (radix count) (windows count)
  rw [Nat.mod_eq_of_lt bound] at reconstructed
  simpa only [radix, ← pow_mul, Nat.mul_comm] using reconstructed

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.nativeWindowed_eq_components
#print axioms LeanCrypto.Proofs.WindowedMSM.radix_capacity
#print axioms LeanCrypto.Proofs.WindowedMSM.digit_sum_mod
#print axioms LeanCrypto.Proofs.WindowedMSM.native_digits_reconstruct
