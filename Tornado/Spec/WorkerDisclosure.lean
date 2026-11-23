import Tornado.Runtime.WorkerProgram

/-! Properties of the capability trace and typed terminal gate used by the
actual worker interpreter. The IO interpreter/OS, opaque proof and signature
outputs, secret-dependent success/failure, timing, resources and managed-memory
remnants are explicit boundaries. No remote anonymity/noninterference or
cryptographic zero-knowledge theorem is asserted. -/

namespace Tornado.Spec.WorkerDisclosure

open Tornado.Runtime.WorkerProgram

/-- The interpreter's returned trace records only capabilities permitted for
the selected mode, including any read/draw which failed. -/
theorem execution_confined (execution : Execution mode α)
    (effect : Effect) (member : effect ∈ execution.effects) :
    effect.allowed mode := execution.confined effect member

theorem protection_precedes_access (execution : Execution mode α) :
    execution.effects.head? = some .protect := execution.protectedFirst

theorem request_reads_require_sign_or_proof (execution : Execution mode α)
    (member : Effect.read .request ∈ execution.effects) :
    mode = .sign ∨ mode = .prove := execution.confined _ member

theorem asset_reads_require_proof (execution : Execution mode α) (asset : Asset)
    (member : Effect.read (.asset asset) ∈ execution.effects) :
    mode = .prove := execution.confined _ member

theorem entropy_requires_proof (execution : Execution mode α)
    (member : Effect.entropy32 ∈ execution.effects) :
    mode = .prove := execution.confined _ member

theorem nonproof_has_no_entropy (execution : Execution mode α)
    (other : mode ≠ .prove) : Effect.entropy32 ∉ execution.effects := by
  intro member
  exact other (entropy_requires_proof execution member)

theorem note_path_is_configured_slot (scope : Scope) :
    scope.path .note = some scope.noteFile := rfl

theorem request_path_is_configured_slot (scope : Scope) :
    scope.path .request = scope.requestFile := rfl

theorem asset_path_has_fixed_suffix (scope : Scope) (asset : Asset) :
    scope.path (.asset asset) = scope.assetsRoot.map (· ++ asset.suffix) := rfl

/-- A terminal value can request one canonical typed stdout line or one
constant stderr diagnostic. There is no arbitrary-string output alternative.
This describes requested writes, conditional on the OS honoring them. -/
theorem terminal_output_shape (output : Terminal mode) :
    (∃ response : Response mode, response.valid = true ∧
      output.stdout = response.encode ++ "\n" ∧ output.stderr = "" ∧
      output.exitCode = 0) ∨
    (output.stdout = "" ∧ output.stderr = failureLine ∧ output.exitCode = 1) := by
  cases output with
  | success response valid => exact Or.inl ⟨response, valid, rfl, rfl, rfl⟩
  | failure => exact Or.inr ⟨rfl, rfl, rfl⟩

theorem invalid_response_is_fixed_failure (response : Response mode)
    (invalid : response.valid ≠ true) :
    terminal (some response) = .failure := by
  simp [terminal, invalid]

theorem absent_response_is_fixed_failure :
    terminal (none : Option (Response mode)) = .failure := rfl

theorem metadata_release_rechecks_canonical_wire
    (metadata : Tornado.Protocol.ProverWorkerWire.Metadata)
    (valid : (Response.metadata metadata).valid = true) :
    (Tornado.Protocol.ProverWorkerWire.Metadata.decode metadata.encode).isOk = true :=
  (Bool.and_eq_true_iff.mp valid).1

theorem released_response_has_no_linebreak (response : Response mode)
    (valid : response.valid = true) : response.singleLine = true :=
  (Bool.and_eq_true_iff.mp valid).2

theorem proof_release_rechecks_request_binding
    (request : Tornado.Protocol.ProverWorkerWire.Request)
    (result : Tornado.Protocol.ProverWorkerWire.Result)
    (valid : (Response.proof request result).valid = true) :
    (result.validateFor request).isOk = true ∧
    (Tornado.Protocol.ProverWorkerWire.Result.decode result.encode).isOk = true := by
  have wire : (Response.proof request result).wireValid = true :=
    (Bool.and_eq_true_iff.mp valid).1
  simpa only [Response.wireValid, Bool.and_eq_true] using wire

theorem signature_release_rechecks_request_binding
    (request : Tornado.Protocol.ProverSignerWire.SignRequest)
    (result : Tornado.Protocol.ProverSignerWire.SignedResult)
    (valid : (Response.signed request result).valid = true) :
    (result.validateFor request).isOk = true ∧
    (Tornado.Protocol.ProverSignerWire.SignedResult.decode result.encode).isOk = true := by
  have wire : (Response.signed request result).wireValid = true :=
    (Bool.and_eq_true_iff.mp valid).1
  simpa only [Response.wireValid, Bool.and_eq_true] using wire

end Tornado.Spec.WorkerDisclosure

#print axioms Tornado.Spec.WorkerDisclosure.execution_confined
#print axioms Tornado.Spec.WorkerDisclosure.protection_precedes_access
#print axioms Tornado.Spec.WorkerDisclosure.request_reads_require_sign_or_proof
#print axioms Tornado.Spec.WorkerDisclosure.asset_reads_require_proof
#print axioms Tornado.Spec.WorkerDisclosure.entropy_requires_proof
#print axioms Tornado.Spec.WorkerDisclosure.nonproof_has_no_entropy
#print axioms Tornado.Spec.WorkerDisclosure.note_path_is_configured_slot
#print axioms Tornado.Spec.WorkerDisclosure.request_path_is_configured_slot
#print axioms Tornado.Spec.WorkerDisclosure.asset_path_has_fixed_suffix
#print axioms Tornado.Spec.WorkerDisclosure.terminal_output_shape
#print axioms Tornado.Spec.WorkerDisclosure.invalid_response_is_fixed_failure
#print axioms Tornado.Spec.WorkerDisclosure.absent_response_is_fixed_failure
#print axioms Tornado.Spec.WorkerDisclosure.metadata_release_rechecks_canonical_wire
#print axioms Tornado.Spec.WorkerDisclosure.released_response_has_no_linebreak
#print axioms Tornado.Spec.WorkerDisclosure.proof_release_rechecks_request_binding
#print axioms Tornado.Spec.WorkerDisclosure.signature_release_rechecks_request_binding
