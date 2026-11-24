import TornadoProofs.Witness.FeistelRound

open Lean Elab Term Meta in
elab "actualMiMCFifth" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.MiMC `LeanCrypto.fifthPower)

set_option autoImplicit false

namespace TornadoProofs.Witness.Execution

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.Groth16R1CS

def fifthValue (value : Nat) : Nat :=
  let square := value * value % scalarPrime
  square * square % scalarPrime * value % scalarPrime

def roundValues (constants : Array Nat) (key round : Nat) (pair : MProd Nat Nat) : MProd Nat Nat :=
  let t := (pair.fst + key + constants[round]!) % scalarPrime
  let next := (pair.snd + fifthValue t) % scalarPrime
  if round < 219 then ⟨next, pair.fst⟩ else ⟨pair.fst, next⟩

def permutationValues (constants : Array Nat) (key left right : Nat) : MProd Nat Nat :=
  (List.range 220).foldl (fun pair round => roundValues constants key round pair) ⟨left, right⟩

def framePair {State : Type} (frame : FeistelFrame State) : MProd Nat Nat := ⟨frame.left, frame.right⟩

def permutationEffect (constants : Array Nat) (key round : Nat) (pair : MProd Nat Nat) :
    Except String (ForInStep (MProd Nat Nat)) :=
  let t := (pair.fst + key + constants[round]!) % scalarPrime
  let next := (pair.snd + fifthValue t) % scalarPrime
  if round < 219 then .ok (.yield ⟨next, pair.fst⟩) else .ok (.yield ⟨pair.fst, next⟩)

theorem native_fifthValue (value : Nat) : actualMiMCFifth value = fifthValue value := rfl

theorem executeFeistelRound_pair (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame output : FeistelFrame Assignment)
    (returned : executeFeistelRound constants stage key round frame = .ok output) :
    framePair output = roundValues constants key round (framePair frame) := by
  unfold executeFeistelRound at returned
  obtain ⟨first, _, returned⟩ := bind_success _ _ output returned
  obtain ⟨second, _, returned⟩ := bind_success _ _ output returned
  by_cases middle : round < 219
  · simp only [middle, ↓reduceIte] at returned
    obtain ⟨third, _, returned⟩ := bind_success _ _ output returned
    obtain ⟨fourth, _, returned⟩ := bind_success _ _ output returned
    have equal : (FeistelFrame.mk fourth _ _) = output := Except.ok.inj returned
    rw [← equal]
    simp only [framePair, roundValues, middle, ↓reduceIte]
    rfl
  · simp only [middle, ↓reduceIte] at returned
    obtain ⟨third, _, returned⟩ := bind_success _ _ output returned
    obtain ⟨fourth, _, returned⟩ := bind_success _ _ output returned
    have equal : (FeistelFrame.mk fourth _ _) = output := Except.ok.inj returned
    rw [← equal]
    simp only [framePair, roundValues, middle, ↓reduceIte]
    rfl

/-- Exact source construction of the independent native MiMC permutation,
including its initial canonicalization and the final nonswapping round. -/
theorem native_permutation_construct (constants : Array Nat) (size : constants.size = 220)
    (left right key : Nat) :
    LeanCrypto.mimcPermutationWith constants left right key =
      .ok (let pair := permutationValues constants (key % scalarPrime) (left % scalarPrime) (right % scalarPrime); (pair.fst, pair.snd)) := by
  simp only [LeanCrypto.mimcPermutationWith, size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [native_fifthValue]
  simp only [bind, Except.bind, pure, Except.pure]
  change ((ForIn.forIn [0:220] (MProd.mk (left % scalarPrime) (right % scalarPrime))
    (permutationEffect constants (key % scalarPrime))) >>= fun pair => pure (pair.fst, pair.snd)) = _
  have effectEqual : permutationEffect constants (key % scalarPrime) =
      (fun round pair => (pure (.yield (roundValues constants (key % scalarPrime) round pair)) :
        Except String (ForInStep (MProd Nat Nat)))) := by
    funext round pair
    unfold permutationEffect roundValues
    split <;> rfl
  rw [effectEqual]
  simp [permutationValues, List.range_eq_range']
  rfl

theorem native_hashPair_construct (constants : Array Nat) (size : constants.size = 220)
    (left right : Nat) (leftBound : left < scalarPrime) (first second : Nat × Nat)
    (firstPermutation : LeanCrypto.mimcPermutationWith constants left 0 0 = .ok first)
    (secondPermutation : LeanCrypto.mimcPermutationWith constants
      ((first.1 + right) % scalarPrime) first.2 0 = .ok second) :
    LeanCrypto.mimcHashPairWith constants left right = .ok second.1 := by
  have nativeLeftBound : left < LeanCrypto.mimcFieldPrime := leftBound
  change LeanCrypto.mimcPermutationWith constants ((first.1 + right) % LeanCrypto.mimcFieldPrime) first.2 0 = .ok second at secondPermutation
  simp [LeanCrypto.mimcHashPairWith, LeanCrypto.mimcMultiHashWith, size,
    Nat.mod_eq_of_lt nativeLeftBound, firstPermutation]
  change ((fun pair : Nat × Nat => pair.1) <$>
    LeanCrypto.mimcPermutationWith constants ((first.1 + right) % LeanCrypto.mimcFieldPrime) first.2 0) = .ok second.1
  rw [secondPermutation]
  rfl

end TornadoProofs.Witness.Execution

#print axioms TornadoProofs.Witness.Execution.native_fifthValue
#print axioms TornadoProofs.Witness.Execution.executeFeistelRound_pair
#print axioms TornadoProofs.Witness.Execution.native_permutation_construct
#print axioms TornadoProofs.Witness.Execution.native_hashPair_construct
