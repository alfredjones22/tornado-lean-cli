import TornadoProofs.Witness.VerificationInverse

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness

/-- Successful original input validation implies the independently defined
note/path source domain, including every direction and the complete parent
chain. No witness or R1CS success is used. -/
theorem prepareInputPrefix_source (input : WithdrawalInput) (output : Array Nat)
    (prepared : prepareInputPrefix input = .ok output) :
    ValidWithdrawal input ∧ output = inputPrefix input := by
  obtain ⟨facts,returned⟩ := prepareInputPrefix_facts input output prepared
  obtain ⟨indexBound,directions,membership⟩ := verifyMimcProof_source input
    facts.siblingWidth facts.directionWidth facts.verified
  exact ⟨⟨facts.nullifierWidth,facts.secretWidth,facts.siblingWidth,facts.directionWidth,
    indexBound,directions,facts.expectedCanonical,facts.expectedRoot,facts.recipient,facts.relayer,
    facts.fee,facts.refund,facts.siblings,facts.commitment,facts.nullifier,membership⟩,returned⟩

theorem prepareInputPrefix_iff_source (input : WithdrawalInput) (output : Array Nat) :
    prepareInputPrefix input = .ok output ↔ ValidWithdrawal input ∧ output = inputPrefix input := by
  constructor
  · exact prepareInputPrefix_source input output
  · rintro ⟨source,rfl⟩
    exact prepareInputPrefix_construct input source

theorem validWithdrawal_iff_prepared (input : WithdrawalInput) :
    ValidWithdrawal input ↔ ∃ output, prepareInputPrefix input = .ok output := by
  constructor
  · intro source
    exact ⟨inputPrefix input,prepareInputPrefix_construct input source⟩
  · rintro ⟨output,prepared⟩
    exact (prepareInputPrefix_source input output prepared).1

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.prepareInputPrefix_source
#print axioms TornadoProofs.Witness.Source.prepareInputPrefix_iff_source
#print axioms TornadoProofs.Witness.Source.validWithdrawal_iff_prepared
