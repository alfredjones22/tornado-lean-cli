import TornadoProofs.Witness.WindowSelection

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjubWindows

def digitAt (bits : Nat → Nat) (offset index : Nat) : Int :=
  nativeNibble (PedersenWindows.selectorIndex (bits (offset+4*index)) (bits (offset+4*index+1))
    (bits (offset+4*index+2)) + 8*bits (offset+4*index+3))

def digits (bits : Nat → Nat) (offset count : Nat) : List Int :=
  (List.range' 0 count).map (digitAt bits offset)

theorem windowValue_append (first second : List Int) :
    windowValue (first ++ second) = windowValue first + (32 : Int)^first.length * windowValue second := by
  induction first with
  | nil => simp [windowValue]
  | cons digit rest ih =>
    simp only [List.cons_append, windowValue, List.length_cons, pow_succ, ih]
    ring

theorem digits_length (bits : Nat → Nat) (offset count : Nat) : (digits bits offset count).length = count := by
  simp only [digits, List.length_map, List.length_range']

theorem digits_valid (bits : Nat → Nat) (offset count : Nat) : ValidDigits (digits bits offset count) := by
  intro digit member
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact nibble_bounds _

theorem digits_succ (bits : Nat → Nat) (offset count : Nat) :
    digits bits offset (count+1) = digits bits offset count ++ [digitAt bits offset count] := by
  unfold digits
  rw [← List.range'_append]
  simp

theorem prefix_scalar_succ (bits : Nat → Nat) (offset count : Nat) :
    windowValue (digits bits offset (count+1)) = windowValue (digits bits offset count) +
      (32 : Int)^count * digitAt bits offset count := by
  rw [digits_succ, windowValue_append, digits_length]
  simp [windowValue]

theorem prefix_group_succ {G : Type} [AddCommGroup G] (base : G) (bits : Nat → Nat) (offset count : Nat) :
    windowValue (digits bits offset (count+1)) • base =
      windowValue (digits bits offset count) • base + digitAt bits offset count • ((32 : Int)^count • base) := by
  rw [prefix_scalar_succ, add_zsmul, mul_comm ((32 : Int)^count), mul_zsmul]

theorem advance_weight {G : Type} [AddCommGroup G] (base : G) (count : Nat) :
    (2 : Nat) • ((2 : Nat) • ((8 : Nat) • ((32 : Int)^count • base))) = (32 : Int)^(count+1) • base := by
  calc
    _ = ((2 : Int)*2*8*(32 : Int)^count) • base := by
      simp only [mul_zsmul, ofNat_zsmul]
    _ = _ := by rw [pow_succ]; congr 1; ring

theorem prefix_scalar_nonzero (bits : Nat → Nat) (offset count : Nat) (positive : 0 < count) :
    windowValue (digits bits offset count) ≠ 0 := by
  have size := digits_length bits offset count
  cases source : digits bits offset count with
  | nil => simp only [source, List.length_nil] at size; omega
  | cons digit rest =>
    apply windowValue_nonzero digit rest
    rw [← source]
    exact digits_valid bits offset count

theorem prefix_scalar_bounded (bits : Nat → Nat) (offset count : Nat) (bounded : count ≤ 50) :
    |windowValue (digits bits offset count)| < (LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder : Int) := by
  apply bounded_window_scalar _ (digits_valid bits offset count)
  simpa only [digits_length] using bounded

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.windowValue_append
#print axioms TornadoProofs.Witness.PedersenReference.digits_length
#print axioms TornadoProofs.Witness.PedersenReference.digits_valid
#print axioms TornadoProofs.Witness.PedersenReference.digits_succ
#print axioms TornadoProofs.Witness.PedersenReference.prefix_scalar_succ
#print axioms TornadoProofs.Witness.PedersenReference.prefix_group_succ
#print axioms TornadoProofs.Witness.PedersenReference.advance_weight
#print axioms TornadoProofs.Witness.PedersenReference.prefix_scalar_nonzero
#print axioms TornadoProofs.Witness.PedersenReference.prefix_scalar_bounded
