import TornadoProofs.Witness.PrefixSlots
import TornadoProofs.Witness.PedersenBounds
import TornadoProofs.Witness.PrefixCanonical

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

/-- Independent original note and path facts. Membership is the native
20-parent MiMC computation on the original leaf/siblings/directions. No VM,
R1CS, Groth16 proof, or final verifier acceptance occurs in this predicate. -/
structure ValidWithdrawal (input : WithdrawalInput) : Prop where
  nullifierWidth : input.note.nullifierBytes.size=31
  secretWidth : input.note.secretBytes.size=31
  siblingWidth : input.proof.siblings.size=20
  directionWidth : input.proof.pathIndices.size=20
  indexBound : input.proof.index < 2^20
  directions : ∀ index<20,input.proof.pathIndices[index]! = (input.proof.index / 2^index) % 2
  expectedCanonical : input.expectedRoot < Field.q
  expectedRoot : input.proof.root=input.expectedRoot
  recipient : input.recipient < 2^160
  relayer : input.relayer < 2^160
  fee : input.fee < Field.q
  refund : input.refund < Field.q
  siblings : ∀ value∈input.proof.siblings,value < Field.q
  commitment : LeanCrypto.pedersenX input.note.preimage=.ok input.note.commitment
  nullifier : LeanCrypto.pedersenX input.note.nullifierBytes=.ok input.note.nullifierHash
  membership : nativePathPrefix Tornado.Crypto.mimcConstants (inputPrefix input) input.note.commitment 20=.ok input.proof.root

theorem valid_commitment_canonical (input : WithdrawalInput) (source : ValidWithdrawal input) :
    input.note.commitment<Field.q := pedersenX_bound input.note.preimage input.note.commitment source.commitment

theorem valid_prefix_size (input : WithdrawalInput) (source : ValidWithdrawal input) :
    (inputPrefix input).size=49 := inputPrefix_size input source.siblingWidth source.directionWidth

theorem valid_prefix_constant (input : WithdrawalInput) : (inputPrefix input)[0]! = 1 := by
  rw [inputPrefix_header input 0 (by decide)]
  rfl

theorem valid_prefix_bits (input : WithdrawalInput) (source : ValidWithdrawal input) :
    (inputPrefix input)[7]! < 2^248 ∧ (inputPrefix input)[8]! < 2^248 := by
  rw [inputPrefix_header input 7 (by decide),inputPrefix_header input 8 (by decide)]
  exact ⟨note_nullifier_248 input.note source.nullifierWidth,note_secret_248 input.note source.secretWidth⟩

theorem valid_prefix_binary (input : WithdrawalInput) (source : ValidWithdrawal input) :
    ∀ index<20,(inputPrefix input)[29+index]! ≤ 1 := by
  intro index bound
  rw [inputPrefix_direction input source.siblingWidth source.directionWidth index bound,source.directions index bound]
  have binary := Nat.mod_lt (input.proof.index / 2^index) (by decide : 0<2)
  omega

theorem valid_prefix_canonical (input : WithdrawalInput) (source : ValidWithdrawal input) :
    Primitive.Bounded (inputPrefix input) := by
  have rootBound : input.proof.root<Field.q := by rw [source.expectedRoot]; exact source.expectedCanonical
  have nullifierHashBound := pedersenX_bound input.note.nullifierBytes input.note.nullifierHash source.nullifier
  have recipientBound : input.recipient<Field.q := Nat.lt_trans source.recipient (by decide)
  have relayerBound : input.relayer<Field.q := Nat.lt_trans source.relayer (by decide)
  have nullifierBound := note_nullifier_Fr input.note source.nullifierWidth
  have secretBound := note_secret_Fr input.note source.secretWidth
  have header : Primitive.Bounded (prefixHeader input) := by
    simpa [Primitive.Bounded,prefixHeader] using
      (show 1<Field.q ∧ input.proof.root<Field.q ∧ input.note.nullifierHash<Field.q ∧
        input.recipient<Field.q ∧ input.relayer<Field.q ∧ input.fee<Field.q ∧ input.refund<Field.q ∧
        input.note.nullifier<Field.q ∧ input.note.secret<Field.q from
          ⟨by decide,rootBound,nullifierHashBound,recipientBound,relayerBound,source.fee,source.refund,nullifierBound,secretBound⟩)
  intro value member
  change value∈((prefixHeader input++input.proof.siblings)++input.proof.pathIndices).toList at member
  simp only [Array.toList_append,List.mem_append] at member
  rcases member with (head | sibling) | direction
  · exact header value head
  · exact source.siblings value (Array.mem_toList_iff.mp sibling)
  · obtain ⟨index,bound,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp direction)
    have small : index<20 := by simpa only [source.directionWidth] using bound
    have valueBit : value≤1 := by
      have direction := source.directions index small
      have smallBit := Nat.mod_lt (input.proof.index / 2^index) (by decide : 0<2)
      rw [getElem!_pos input.proof.pathIndices index bound,equal] at direction
      omega
    exact Nat.lt_of_le_of_lt valueBit (by decide)

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.valid_commitment_canonical
#print axioms TornadoProofs.Witness.Source.valid_prefix_size
#print axioms TornadoProofs.Witness.Source.valid_prefix_constant
#print axioms TornadoProofs.Witness.Source.valid_prefix_bits
#print axioms TornadoProofs.Witness.Source.valid_prefix_binary
#print axioms TornadoProofs.Witness.Source.valid_prefix_canonical
