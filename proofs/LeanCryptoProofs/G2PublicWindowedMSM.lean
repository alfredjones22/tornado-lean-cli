import LeanCryptoProofs.G2NativeWindowedMSM
import LeanCryptoProofs.G2NormalizationGroupLaw

open Lean Elab Term Meta
elab "actualMsmG2Point" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.MSM `LeanCrypto.Groth16.MSM.g2Point)

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

open LeanCrypto.BN254.G2 LeanCrypto.Groth16.Types LeanCrypto.Proofs.BN254G2Jacobian

abbrev nativeG2Point (point : DecodedG2) : Except String Jacobian := actualMsmG2Point point

theorem nativeG2Point_admissible (input : DecodedG2) (point : Jacobian)
    (success : nativeG2Point input = .ok point) : Admissible point := by
  cases input with
  | identity =>
    change Except.ok Jacobian.infinity = Except.ok point at success
    cases success
    exact infinity_admissible
  | point affine =>
    change (if affine.onCurve then Except.ok (Jacobian.ofAffine affine)
      else Except.error "Groth16 G2 point is not on the twist.") = Except.ok point at success
    split at success
    · rename_i onCurve
      cases success
      exact ofAffine_admissible affine onCurve
    · cases success

theorem msmG2_source (points : Array DecodedG2) (scalars : Array Nat) :
    LeanCrypto.Groth16.MSM.msmG2 points scalars =
      if points.size != scalars.size then .error "Groth16 G2 MSM point and scalar counts differ."
      else if !scalars.all (· < LeanCrypto.Groth16.MSM.order) then
        .error "Groth16 G2 MSM scalar is outside BN254 Fr."
      else (points.mapM nativeG2Point).map (fun decoded =>
        nativeWindowed decoded scalars Jacobian.infinity Jacobian.add Jacobian.double) := by
  unfold LeanCrypto.Groth16.MSM.msmG2
  split
  · rfl
  · split
    · rfl
    · simp [Array.mapM_eq_foldlM]
      rfl

private theorem list_mapM_source_g2 {A B : Type} (f : A → Except String B)
    (input : List A) (output : List B) (success : input.mapM f = .ok output) :
    List.Forall₂ (fun a b => f a = .ok b) input output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at success
    cases success
    exact .nil
  | cons head tail ih =>
    cases first : f head with
    | error message => simp [List.mapM_cons, first, bind, Except.bind] at success
    | ok value =>
      cases rest : tail.mapM f with
      | error message => simp [List.mapM_cons, first, rest, bind, Except.bind] at success
      | ok values =>
        simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at success
        cases success
        exact .cons first (ih values rest)

private theorem array_mapM_source_g2 {A B : Type} (f : A → Except String B)
    (input : Array A) (output : Array B) (success : input.mapM f = .ok output) :
    List.Forall₂ (fun a b => f a = .ok b) input.toList output.toList := by
  rw [Array.mapM_eq_mapM_toList] at success
  cases decoded : input.toList.mapM f with
  | error message => simp [decoded] at success
  | ok values =>
    simp only [decoded] at success
    change Except.ok values.toArray = Except.ok output at success
    cases success
    exact list_mapM_source_g2 f input.toList values decoded

private theorem ordered_points_admissible_g2 {inputs : List DecodedG2} {outputs : List Jacobian}
    (ordered : List.Forall₂ (fun input output => nativeG2Point input = .ok output) inputs outputs) :
    ∀ point ∈ outputs, Admissible point := by
  induction ordered with
  | nil => simp
  | @cons input output inputs outputs built tail ih =>
    intro point member
    rcases List.mem_cons.mp member with equal | member
    · subst point
      exact nativeG2Point_admissible input output built
    · exact ih point member

/-- Success of the actual public msmG2 carries the exact ordered decoding
of the original input array and its scalar-weighted native group meaning. -/
theorem msmG2_success_sum (points : Array DecodedG2) (scalars : Array Nat) (result : Jacobian)
    (success : LeanCrypto.Groth16.MSM.msmG2 points scalars = .ok result) :
    ∃ decoded : Array Jacobian,
      points.mapM nativeG2Point = .ok decoded ∧
      List.Forall₂ (fun input point => nativeG2Point input = .ok point) points.toList decoded.toList ∧
      decoded.size = points.size ∧ points.size = scalars.size ∧
      scalars.all (· < LeanCrypto.Groth16.MSM.order) = true ∧ Admissible result ∧
      LeanCrypto.Proofs.BN254G2Group.groupPoint result =
        ∑ index ∈ Finset.range points.size,
          (scalars[index]! % LeanCrypto.Groth16.MSM.order) •
            LeanCrypto.Proofs.BN254G2Group.groupPoint decoded[index]! := by
  rw [msmG2_source] at success
  split at success
  · cases success
  · rename_i counts
    have countEqual : points.size = scalars.size := by simpa using counts
    split at success
    · cases success
    · rename_i bounds
      have allScalars : scalars.all (· < LeanCrypto.Groth16.MSM.order) = true := by simpa using bounds
      cases decodedSource : points.mapM nativeG2Point with
      | error message => simp [decodedSource, Except.map] at success
      | ok decoded =>
        simp only [decodedSource, Except.map, Except.ok.injEq] at success
        cases success
        have ordered := array_mapM_source_g2 nativeG2Point points decoded decodedSource
        have shape : decoded.size = points.size := by simpa using ordered.length_eq.symm
        have admitted : ∀ point ∈ decoded, Admissible point := by
          intro point member
          exact ordered_points_admissible_g2 ordered point (Array.mem_def.mp member)
        have canonical : ∀ index, index < decoded.size → scalars[index]! < LeanCrypto.Groth16.MSM.order := by
          intro index bounded
          have scalarIndex : index < scalars.size := by omega
          have value := (Array.all_eq_true.mp allScalars) index scalarIndex
          simpa [scalarIndex] using value
        refine ⟨decoded, rfl, ordered, shape, countEqual, allScalars,
          native_g2_raw_windowed_admissible decoded scalars admitted, ?_⟩
        rw [native_g2_raw_windowed_sum decoded scalars admitted canonical, shape]
        apply Finset.sum_congr rfl
        intro index member
        rw [Nat.mod_eq_of_lt (canonical index (by have := Finset.mem_range.mp member; omega))]

/-- The public MSM's actual normalizer constructs the corresponding
mathematical weighted sum; no final checker success is among the premises. -/
theorem msmG2_success_normalized_sum (points : Array DecodedG2) (scalars : Array Nat) (result : Jacobian)
    (success : LeanCrypto.Groth16.MSM.msmG2 points scalars = .ok result) :
    ∃ (decoded : Array Jacobian) (output : Option Affine),
      points.mapM nativeG2Point = .ok decoded ∧
      List.Forall₂ (fun input point => nativeG2Point input = .ok point) points.toList decoded.toList ∧
      result.toAffine = .ok output ∧
      LeanCrypto.Proofs.BN254G2Group.Represents output
        (∑ index ∈ Finset.range points.size,
          (scalars[index]! % LeanCrypto.Groth16.MSM.order) •
            LeanCrypto.Proofs.BN254G2Group.groupPoint decoded[index]!) := by
  obtain ⟨decoded, source, ordered, _, _, _, admitted, meaning⟩ := msmG2_success_sum points scalars result success
  obtain ⟨output, built, represented⟩ :=
    LeanCrypto.Proofs.BN254G2Group.toAffine_represents_groupPoint result admitted
  exact ⟨decoded, output, source, ordered, built, meaning ▸ represented⟩

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.nativeG2Point_admissible
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG2_source

#print axioms LeanCrypto.Proofs.WindowedMSM.list_mapM_source_g2
#print axioms LeanCrypto.Proofs.WindowedMSM.array_mapM_source_g2
#print axioms LeanCrypto.Proofs.WindowedMSM.ordered_points_admissible_g2
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG2_success_sum
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG2_success_normalized_sum
