import TornadoProofs.Witness.WithdrawalSource

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM

def verificationEffect (constants : Array Nat) (input : WithdrawalInput) (index current : Nat) :
    Except String (ForInStep Nat) := do
  let side := input.proof.pathIndices[index]!
  let sibling := input.proof.siblings[index]!
  if side != (input.proof.index / 2^index) % 2 then
    throw "MiMC proof direction differs from its index"
  if side==0 then
    let next ← LeanCrypto.mimcHashPairWith constants current sibling
    pure (.yield next)
  else if side==1 then
    let next ← LeanCrypto.mimcHashPairWith constants sibling current
    pure (.yield next)
  else throw "Invalid MiMC path direction"

theorem forIn_actions_foldlM {A B : Type} (items : List A) (action : A → B → Except String B) (initial : B) :
    forIn items initial (fun item state => do
      let next ← action item state
      pure (ForInStep.yield next))=items.foldlM (fun state item => action item state) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons,List.foldlM_cons]
    simp only [bind_assoc,pure_bind]
    apply congrArg (fun continuation => action head initial >>= continuation)
    funext middle
    exact ih middle

theorem verificationEffect_source (constants : Array Nat) (input : WithdrawalInput)
    (source : ValidWithdrawal input) (index current : Nat) (bound : index<20) :
    verificationEffect constants input index current=(do
      let next ← nativePathStep constants (inputPrefix input) index current
      pure (ForInStep.yield next)) := by
  have direction := source.directions index bound
  have directionBound : input.proof.pathIndices[index]! < 2 := by
    rw [direction]
    exact Nat.mod_lt _ (by decide)
  have binary : input.proof.pathIndices[index]! = 0 ∨ input.proof.pathIndices[index]! = 1 := by omega
  unfold nativePathStep verificationEffect
  rw [inputPrefix_sibling input source.siblingWidth index bound,
    inputPrefix_direction input source.siblingWidth source.directionWidth index bound]
  have matched : (input.proof.pathIndices[index]! != (input.proof.index / 2^index) % 2)=false := by
    simp only [direction,bne_self_eq_false]
  simp only [matched,Bool.false_eq_true,↓reduceIte,pure_bind]
  rcases binary with zero | one
  · simp only [zero,beq_self_eq_true,↓reduceIte,dualMuxValues]
  · simp only [one,show (1==0)=false from rfl,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,dualMuxValues]

theorem verifyMimcProof_effects (constants : Array Nat) (input : WithdrawalInput) :
    LeanCrypto.verifyMimcProofWith constants input.note.commitment input.proof=(do
      if input.proof.siblings.size != input.proof.pathIndices.size || input.proof.siblings.size>20 then
        throw "Invalid MiMC proof depth"
      if input.proof.index >= 2^input.proof.siblings.size then
        throw "MiMC proof index exceeds its depth"
      let current ← forIn (List.range input.proof.siblings.size) input.note.commitment (verificationEffect constants input)
      pure (current==input.proof.root)) := by
  unfold LeanCrypto.verifyMimcProofWith
  simp only [pure_bind,forIn_range_zero]
  rfl

theorem valid_membership_construct (input : WithdrawalInput) (source : ValidWithdrawal input) :
    LeanCrypto.verifyMimcProof input.note.commitment input.proof=.ok true := by
  have nativeLoop : (forIn (List.range 20) input.note.commitment (fun index current => do
      let next ← nativePathStep Tornado.Crypto.mimcConstants (inputPrefix input) index current
      pure (ForInStep.yield next)))=.ok input.proof.root := by
    rw [forIn_actions_foldlM]
    exact source.membership
  have actualLoop := forIn_construct_from_public_mem (List.range 20) _
    (verificationEffect Tornado.Crypto.mimcConstants input) id (fun _ => True)
    (fun _ _ _ _ _ _ => trivial)
    (fun index member before next returned _ => by
      simp only [id_eq]
      rw [verificationEffect_source Tornado.Crypto.mimcConstants input source index before (List.mem_range.mp member)]
      cases next <;> simpa only [mapStep,id_eq] using returned)
    input.note.commitment input.proof.root nativeLoop trivial
  have actualLoop' : forIn (List.range 20) input.note.commitment
      (verificationEffect Tornado.Crypto.mimcConstants input)=.ok input.proof.root := by
    simpa only [id_eq] using actualLoop.2
  unfold LeanCrypto.verifyMimcProof
  rw [verifyMimcProof_effects]
  have indexValid : ¬ input.proof.index >= 2^20 := Nat.not_le.mpr source.indexBound
  simp only [source.siblingWidth,source.directionWidth,bne_self_eq_false,show ¬20>20 from by decide,
    decide_false,Bool.false_or,Bool.false_eq_true,↓reduceIte,indexValid,pure_bind]
  rw [actualLoop']
  simp only [bind,Except.bind,beq_self_eq_true,pure,Except.pure]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.forIn_actions_foldlM
#print axioms TornadoProofs.Witness.Source.verificationEffect_source
#print axioms TornadoProofs.Witness.Source.verifyMimcProof_effects
#print axioms TornadoProofs.Witness.Source.valid_membership_construct
