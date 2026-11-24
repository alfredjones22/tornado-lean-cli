import TornadoProofs.Witness.PreparedFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open Tornado.Protocol.WitnessVM
open TornadoProofs.Witness.Execution

theorem verificationEffect_direction (constants : Array Nat) (input : WithdrawalInput)
    (index current : Nat) (step : ForInStep Nat)
    (returned : verificationEffect constants input index current = .ok step) :
    input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2 := by
  by_contra different
  have mismatch : (input.proof.pathIndices[index]! != (input.proof.index / 2^index) % 2) = true := bne_iff_ne.mpr different
  simp [verificationEffect,mismatch,bind,Except.bind] at returned

/-- The source routing equality suffices; this lemma does not require a
ValidWithdrawal or any native witness/R1CS acceptance. -/
theorem verificationEffect_routing (constants : Array Nat) (input : WithdrawalInput)
    (siblings : input.proof.siblings.size = 20) (directions : input.proof.pathIndices.size = 20)
    (index current : Nat) (bound : index < 20)
    (direction : input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2) :
    verificationEffect constants input index current = (do
      let next ← nativePathStep constants (inputPrefix input) index current
      pure (ForInStep.yield next)) := by
  have directionBound : input.proof.pathIndices[index]! < 2 := by
    rw [direction]
    exact Nat.mod_lt _ (by decide)
  have binary : input.proof.pathIndices[index]! = 0 ∨ input.proof.pathIndices[index]! = 1 := by omega
  unfold nativePathStep verificationEffect
  rw [inputPrefix_sibling input siblings index bound,inputPrefix_direction input siblings directions index bound]
  have matched : (input.proof.pathIndices[index]! != (input.proof.index / 2^index) % 2) = false := by
    simp only [direction,bne_self_eq_false]
  simp only [matched,Bool.false_eq_true,↓reduceIte,pure_bind]
  rcases binary with zero | one
  · simp only [zero,beq_self_eq_true,↓reduceIte,dualMuxValues]
  · simp only [one,show (1==0)=false from rfl,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,dualMuxValues]

theorem verificationEffect_success (constants : Array Nat) (input : WithdrawalInput)
    (siblings : input.proof.siblings.size = 20) (directions : input.proof.pathIndices.size = 20)
    (index current : Nat) (bound : index < 20) (step : ForInStep Nat)
    (returned : verificationEffect constants input index current = .ok step) :
    input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2 ∧
      ∃ next, ForInStep.yield next = step ∧ nativePathStep constants (inputPrefix input) index current = .ok next := by
  have direction := verificationEffect_direction constants input index current step returned
  rw [verificationEffect_routing constants input siblings directions index current bound direction] at returned
  obtain ⟨next,computed,finished⟩ := bind_success _ _ step returned
  exact ⟨direction,next,Except.ok.inj finished,computed⟩

/-- Every successful action yields; therefore a successful original loop
has checked every original direction and computes the complete native fold. -/
theorem verificationLoop_source (constants : Array Nat) (input : WithdrawalInput)
    (siblings : input.proof.siblings.size = 20) (directions : input.proof.pathIndices.size = 20)
    (items : List Nat) (bounds : ∀ index∈items, index < 20) (initial final : Nat)
    (returned : forIn items initial (verificationEffect constants input) = .ok final) :
    (∀ index∈items, input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2) ∧
      items.foldlM (fun current index => nativePathStep constants (inputPrefix input) index current) initial = .ok final := by
  induction items generalizing initial with
  | nil =>
    have equal : initial = final := Except.ok.inj returned
    exact ⟨by simp,by simpa only [List.foldlM_nil,pure,Except.pure] using congrArg Except.ok equal⟩
  | cons index tail ih =>
    cases first : verificationEffect constants input index initial with
    | error message => simp [List.forIn_cons,first,bind,Except.bind] at returned
    | ok step =>
      obtain ⟨direction,next,equal,computed⟩ := verificationEffect_success constants input siblings directions
        index initial (bounds index (by simp)) step first
      cases equal
      have rest : forIn tail next (verificationEffect constants input) = .ok final := by
        simpa only [List.forIn_cons,first,bind,Except.bind,pure,Except.pure] using returned
      have tailBounds : ∀ index∈tail, index < 20 := fun index member => bounds index (by simp [member])
      obtain ⟨tailDirections,folded⟩ := ih tailBounds next rest
      refine ⟨?_,?_⟩
      · intro other member
        rcases List.mem_cons.mp member with equal | member
        · simpa only [equal] using direction
        · exact tailDirections other member
      · change (nativePathStep constants (inputPrefix input) index initial >>= fun current =>
          tail.foldlM (fun current index => nativePathStep constants (inputPrefix input) index current) current) = .ok final
        rw [computed]
        exact folded

theorem verifyMimcProof_source (input : WithdrawalInput)
    (siblings : input.proof.siblings.size = 20) (directions : input.proof.pathIndices.size = 20)
    (verified : LeanCrypto.verifyMimcProof input.note.commitment input.proof = .ok true) :
    input.proof.index < 2^20 ∧
      (∀ index < 20, input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2) ∧
      nativePathPrefix Tornado.Crypto.mimcConstants (inputPrefix input) input.note.commitment 20 = .ok input.proof.root := by
  unfold LeanCrypto.verifyMimcProof at verified
  rw [verifyMimcProof_effects] at verified
  simp only [siblings,directions,bne_self_eq_false,show ¬20>20 from by decide,decide_false,
    Bool.false_or,Bool.false_eq_true,↓reduceIte,pure_bind] at verified
  by_cases outside : input.proof.index >= 2^20
  · simp only [outside,↓reduceIte] at verified
    cases verified
  · simp only [outside,↓reduceIte] at verified
    obtain ⟨root,computed,finished⟩ := bind_success _ _ true verified
    have check : (root == input.proof.root) = true := by
      simpa only [pure,Except.pure,Except.ok.injEq] using finished
    have equal : root = input.proof.root := beq_iff_eq.mp check
    have source := verificationLoop_source Tornado.Crypto.mimcConstants input siblings directions
      (List.range 20) (fun _ member => List.mem_range.mp member) input.note.commitment root computed
    refine ⟨by omega,fun index bound => source.1 index (List.mem_range.mpr bound),?_⟩
    simpa only [nativePathPrefix,equal] using source.2

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.verificationEffect_direction
#print axioms TornadoProofs.Witness.Source.verificationEffect_routing
#print axioms TornadoProofs.Witness.Source.verificationEffect_success
#print axioms TornadoProofs.Witness.Source.verificationLoop_source
#print axioms TornadoProofs.Witness.Source.verifyMimcProof_source
