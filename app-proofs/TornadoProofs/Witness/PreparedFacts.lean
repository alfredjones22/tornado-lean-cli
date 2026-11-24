import TornadoProofs.Witness.InputConstruction

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

/-- Facts read directly from successful original input validation. The final
member is the native path validator, not the witness or R1CS checker. -/
structure PreparedFacts (input : WithdrawalInput) : Prop where
  nullifierWidth : input.note.nullifierBytes.size = 31
  secretWidth : input.note.secretBytes.size = 31
  siblingWidth : input.proof.siblings.size = 20
  directionWidth : input.proof.pathIndices.size = 20
  expectedCanonical : input.expectedRoot < Field.q
  expectedRoot : input.proof.root = input.expectedRoot
  recipient : input.recipient < 2^160
  relayer : input.relayer < 2^160
  fee : input.fee < Field.q
  refund : input.refund < Field.q
  siblings : ∀ value∈input.proof.siblings, value < Field.q
  commitment : LeanCrypto.pedersenX input.note.preimage = .ok input.note.commitment
  nullifier : LeanCrypto.pedersenX input.note.nullifierBytes = .ok input.note.nullifierHash
  verified : LeanCrypto.verifyMimcProof input.note.commitment input.proof = .ok true

theorem prepareInputPrefix_facts (input : WithdrawalInput) (output : Array Nat)
    (prepared : prepareInputPrefix input = .ok output) :
    PreparedFacts input ∧ output = inputPrefix input := by
  unfold prepareInputPrefix at prepared
  simp only [pure,Except.pure,bind,Except.bind] at prepared
  split at prepared
  · cases prepared
  · rename_i bytesChecked
    split at prepared
    · cases prepared
    · rename_i depthChecked
      split at prepared
      · cases prepared
      · rename_i expectedChecked
        split at prepared
        · cases prepared
        · rename_i addressesChecked
          split at prepared
          · cases prepared
          · rename_i feesChecked
            split at prepared
            · cases prepared
            · rename_i siblingsChecked
              obtain ⟨commitment,commitmentBuilt,prepared⟩ := bind_success (LeanCrypto.pedersenX input.note.preimage) _ output prepared
              split at prepared
              · cases prepared
              · rename_i commitmentChecked
                obtain ⟨nullifier,nullifierBuilt,prepared⟩ := bind_success (LeanCrypto.pedersenX input.note.nullifierBytes) _ output prepared
                split at prepared
                · cases prepared
                · rename_i nullifierChecked
                  obtain ⟨verified,verifiedBuilt,prepared⟩ := bind_success (LeanCrypto.verifyMimcProof input.note.commitment input.proof) _ output prepared
                  cases verified with
                  | false => simp at prepared
                  | true =>
                    have returnedPrefix : output = inputPrefix input := by
                      simpa [bind,Except.bind,pure,Except.pure] using prepared.symm
                    have bytes : input.note.nullifierBytes.size = 31 ∧ input.note.secretBytes.size = 31 := by
                      simpa only [Bool.or_eq_true,bne_iff_ne,not_or,not_not] using bytesChecked
                    have depth : input.proof.siblings.size = 20 ∧ input.proof.pathIndices.size = 20 := by
                      simpa only [Bool.or_eq_true,bne_iff_ne,not_or,not_not] using depthChecked
                    have expected : input.expectedRoot < Field.q ∧ input.proof.root = input.expectedRoot := by
                      simpa only [Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne,not_or,not_not,Nat.not_le] using expectedChecked
                    have addresses : input.recipient < 2^160 ∧ input.relayer < 2^160 := by
                      simpa only [Bool.or_eq_true,decide_eq_true_eq,not_or,Nat.not_le] using addressesChecked
                    have fees : input.fee < Field.q ∧ input.refund < Field.q := by
                      simpa only [Bool.or_eq_true,decide_eq_true_eq,not_or,Nat.not_le] using feesChecked
                    have siblings : ∀ value∈input.proof.siblings, value < Field.q := by
                      intro value member
                      obtain ⟨index,bound,equal⟩ := Array.mem_iff_getElem.mp member
                      have checked := Array.any_eq_false.mp (Bool.eq_false_iff.mpr siblingsChecked) index bound
                      have small : input.proof.siblings[index] < Field.q := by
                        simpa only [decide_eq_true_eq,Nat.not_le] using checked
                      simpa only [equal] using small
                    have commitmentEqual : commitment = input.note.commitment :=
                      bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr commitmentChecked)
                    have nullifierEqual : nullifier = input.note.nullifierHash :=
                      bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr nullifierChecked)
                    exact ⟨⟨bytes.1,bytes.2,depth.1,depth.2,expected.1,expected.2,
                      addresses.1,addresses.2,fees.1,fees.2,siblings,
                      by simpa only [commitmentEqual] using commitmentBuilt,
                      by simpa only [nullifierEqual] using nullifierBuilt,verifiedBuilt⟩,returnedPrefix⟩

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.prepareInputPrefix_facts
