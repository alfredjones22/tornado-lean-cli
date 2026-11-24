import TornadoProofs.Witness.FeistelRowProgram

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS
open TornadoProofs.Witness.Execution
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

theorem nativeT_model (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) :
    model (nativeT constants key round frame) = model frame.left + model key + model constants[round]! := by
  change model ((frame.left + key + constants[round]!) % Q) = _
  rw [model_mod]
  simp only [model, Nat.cast_add]

theorem nativeSquare_model (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) :
    model (nativeSquare constants key round frame) =
      model (nativeT constants key round frame) * model (nativeT constants key round frame) := by
  change model (LeanCrypto.Groth16.FFT.mul _ _) = _
  exact model_mul _ _

theorem nativeFourth_model (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) :
    model (nativeFourth constants key round frame) =
      model (nativeSquare constants key round frame) * model (nativeSquare constants key round frame) := by
  change model (LeanCrypto.Groth16.FFT.mul _ _) = _
  exact model_mul _ _

theorem nativeNext_model (constants : Array Nat) (key round : Nat) (frame : FeistelFrame Assignment) :
    model (nativeNext constants key round frame) = model frame.right +
      model (nativeFourth constants key round frame) * model (nativeT constants key round frame) := by
  change model (LeanCrypto.Groth16.FFT.add frame.right (LeanCrypto.Groth16.FFT.mul _ _)) = _
  simp only [model_add, model_mul]

/-- Every actual round's stored values satisfy precisely the equations
emitted by the frozen public local-row generator. -/
theorem rowsRound_sound (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (stage : Feistel) (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index) = assignment index)
    (key round : Nat) (keyValue : assignment stage.key = model key)
    (before after : FeistelFrame Assignment) (rows : RowsFrame)
    (executed : executeFeistelRound constants stage key round before = .ok after)
    (respects : Respects assignment after.state)
    (valid : SystemSatisfied assignment rows.snd.fst) (meaning : FrameMeaning assignment rows before) :
    SystemSatisfied assignment (rowsRound nodes compiled constants stage round rows).snd.fst ∧
      (round < 219 → FrameMeaning assignment (rowsRound nodes compiled constants stage round rows) after) := by
  let row := signalLinear nodes compiled
  have rowV : ∀ index, linearValue assignment (row index) = assignment index := rowValue
  let t := sumLinear [rows.fst, row stage.key, constantLinear constants[round]!]
  have tValue : linearValue assignment t = model (nativeT constants key round before) := by
    simp only [t, sumLinear_value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      constantLinear_value assignment constant, meaning.1, rowV, keyValue, add_zero]
    rw [nativeT_model]
    ring
  have writes := executeRound_writes constants stage key round before after executed
  have squareValue : assignment stage.t2[round]! = model (nativeSquare constants key round before) :=
    respects _ _ writes.2.1
  have fourthValue : assignment stage.t4[round]! = model (nativeFourth constants key round before) :=
    respects _ _ writes.2.2.1
  let first := rows.snd.fst.product stage.t2[round]! t t
  have firstValid : SystemSatisfied assignment first := by
    apply product_emit assignment constant rows.snd.fst stage.t2[round]! t t valid
    rw [tValue, squareValue, nativeSquare_model]
  let second := first.product stage.t4[round]! (row stage.t2[round]!) (row stage.t2[round]!)
  have secondValid : SystemSatisfied assignment second := by
    apply product_emit assignment constant first stage.t4[round]! (row stage.t2[round]!) (row stage.t2[round]!) firstValid
    rw [rowValue, squareValue, fourthValue, nativeFourth_model]
  by_cases middle : round < 219
  · have assigned := writes.2.2.2
    rw [if_pos middle] at assigned
    have leftValue := respects _ _ assigned.1
    have rightValue := respects _ _ assigned.2
    let third := second.constraint (row stage.t4[round]!) t (minusLinear (row stage.leftRounds[round]!) rows.snd.snd)
    have thirdValid : SystemSatisfied assignment third := by
      apply constraint_emit assignment constant second _ _ _ secondValid
      rw [rowValue, fourthValue, tValue, minusLinear_value, rowValue, leftValue, meaning.2, nativeNext_model]
      ring
    have fourthValid := equality_emit assignment third stage.rightRounds[round]! rows.fst thirdValid
      (rightValue.trans meaning.1.symm)
    refine ⟨?_, ?_⟩
    · simpa only [rowsRound, middle, ↓reduceIte] using fourthValid
    · intro _
      have pair := executeFeistelRound_pair constants stage key round before after executed
      have afterLeft : after.left = nativeNext constants key round before := by
        simpa only [framePair, roundValues, middle, ↓reduceIte, nativeNext, nativeFourth,
          nativeSquare, nativeT, fifthValue] using congrArg MProd.fst pair
      have afterRight : after.right = before.left := by
        simpa only [framePair, roundValues, middle, ↓reduceIte] using congrArg MProd.snd pair
      constructor
      · simp only [rowsRound, middle, ↓reduceIte]
        rw [rowValue, leftValue, afterLeft]
      · simp only [rowsRound, middle, ↓reduceIte]
        rw [rowValue, rightValue, afterRight]
  · have assigned := writes.2.2.2
    rw [if_neg middle] at assigned
    have leftValue := respects _ _ assigned.1
    have rightValue := respects _ _ assigned.2
    let third := second.equality stage.leftOutput rows.fst
    have thirdValid : SystemSatisfied assignment third :=
      equality_emit assignment second stage.leftOutput rows.fst secondValid (leftValue.trans meaning.1.symm)
    have fourthValid : SystemSatisfied assignment
        (third.constraint (row stage.t4[round]!) t (minusLinear (row stage.rightOutput) rows.snd.snd)) := by
      apply constraint_emit assignment constant third _ _ _ thirdValid
      rw [rowValue, fourthValue, tValue, minusLinear_value, rowValue, rightValue, meaning.2, nativeNext_model]
      ring
    refine ⟨?_, fun contradiction => False.elim (middle contradiction)⟩
    simpa only [rowsRound, middle, ↓reduceIte] using fourthValid

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.nativeT_model
#print axioms TornadoProofs.Witness.Local.nativeSquare_model
#print axioms TornadoProofs.Witness.Local.nativeFourth_model
#print axioms TornadoProofs.Witness.Local.nativeNext_model
#print axioms TornadoProofs.Witness.Local.rowsRound_sound
