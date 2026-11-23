import Lean

namespace Tornado.Policy

/-- The finite simulation outcomes accepted by the TypeScript CLI. -/
inductive SimulationStatus where
  | passed | failed | unavailable
  deriving Repr, BEq, DecidableEq

inductive AvailabilityReason where
  | transport | unsupported | other
  deriving Repr, BEq, DecidableEq

structure Simulation where
  status : SimulationStatus
  userOpHash : String
  checkedAt : Int
  availabilityReason : AvailabilityReason := .other
  deriving Repr

structure BatchQuote where
  userOpHash : String
  estimated : Bool
  deriving Repr

/-- This matches the pure admission predicate in `batch-simulation.ts`.
    It deliberately has no lower freshness bound, matching the source. -/
def canSubmitSimulation (result : Simulation) (quote : BatchQuote) (now : Int) : Bool :=
  result.userOpHash.toLower == quote.userOpHash.toLower &&
  decide (now - result.checkedAt < 300000) &&
  (match result.status with
   | .passed => true
   | .failed => false
   | .unavailable =>
       (result.availabilityReason == .transport || result.availabilityReason == .unsupported) &&
       quote.estimated)

structure RelayerFeeInput where
  amount : Nat
  fee : Nat
  serviceFeeBps : Nat
  deriving Repr

structure RelayerFeeResult where
  fee : Nat
  net : Nat
  serviceFee : Nat
  networkFee : Nat
  deriving Repr, DecidableEq

/-- The arithmetic guards in `validateRelayerWithdrawal`, stated as a proposition. -/
def relayerFeeWithinLimits (input : RelayerFeeInput) : Prop :=
  1 ≤ input.serviceFeeBps ∧ input.serviceFeeBps < 100 ∧
  0 < input.fee ∧ input.fee < input.amount ∧
  input.fee * 10000 ≤ input.amount * 2000

instance (input : RelayerFeeInput) : Decidable (relayerFeeWithinLimits input) := by
  unfold relayerFeeWithinLimits
  infer_instance

/-- Arithmetic subset of the captured relayer fee validator. The caller must
    separately validate note, proof, recipient, registered relayer and endpoint. -/
def validateRelayerFee (input : RelayerFeeInput) : Option RelayerFeeResult :=
  if relayerFeeWithinLimits input then
    let serviceFee := input.amount * input.serviceFeeBps / 10000
    if input.fee < serviceFee then none
    else some { fee := input.fee, net := input.amount - input.fee, serviceFee := serviceFee, networkFee := input.fee - serviceFee }
  else none

/-- A minimal native state machine for the one-note signing/exposure boundary.
    It is a policy core, not the file, SDK, or RPC implementation. -/
inductive AttemptPhase where
  | fresh | approved | signed | reserved | exposed | submitted | unknown | confirmed
  deriving Repr, BEq, DecidableEq

structure Attempt where
  phase : AttemptPhase := .fresh
  reviewedHash : Option String := none
  signedHash : Option String := none
  reservedHash : Option String := none
  sends : Nat := 0
  deriving Repr

/-- Decoded chain evidence for a direct one-note withdrawal. The decoder and
    selected RPC are separate trust boundaries; this structure does not
    authenticate either one. -/
structure ConfirmationEvidence where
  receiptSuccess : Bool
  entryPointEventMatches : Bool
  withdrawalEventMatches : Bool
  deriving Repr

inductive AttemptAction where
  | approve (hash : String)
  | sign (hash : String)
  | reserve
  | expose
  | send
  | markUnknown
  | confirm (evidence : ConfirmationEvidence)
  deriving Repr

/-- Fail-closed transition function. A signed payload must equal the reviewed
    hash; reservation must equal both before exposure or one submission. -/
def stepAttempt (state : Attempt) (action : AttemptAction) : Except String Attempt :=
  match action with
  | .approve hash =>
      if state.phase == .fresh && hash != "" then
        .ok { state with phase := .approved, reviewedHash := some hash }
      else .error "An unresolved attempt blocks approval."
  | .sign hash =>
      if state.phase == .approved && state.reviewedHash == some hash then
        .ok { state with phase := .signed, signedHash := some hash }
      else .error "The signed payload differs from the approved hash."
  | .reserve =>
      if state.phase == .signed && state.reviewedHash == state.signedHash &&
          state.signedHash.isSome then
        .ok { state with phase := .reserved, reservedHash := state.signedHash }
      else .error "The candidate is not ready for reservation."
  | .expose =>
      if state.phase == .reserved && state.reservedHash == state.signedHash &&
          state.reservedHash.isSome then
        .ok { state with phase := .exposed }
      else .error "Exposure requires a matching reservation."
  | .send =>
      match state.phase with
      | .exposed =>
          if state.reservedHash == state.signedHash &&
              state.reservedHash.isSome && state.sends == 0 then
            .ok { state with phase := .submitted, sends := 1 }
          else .error "Submission requires a matching reservation and no earlier send."
      | _ => .error "Submission requires a matching reservation and no earlier send."
  | .markUnknown =>
      if state.phase == .exposed || state.phase == .submitted then
        .ok { state with phase := .unknown }
      else .error "Only an exposed or submitted attempt can become unknown."
  | .confirm evidence =>
      if (state.phase == .exposed || state.phase == .submitted ||
          state.phase == .unknown) &&
          evidence.receiptSuccess && evidence.entryPointEventMatches &&
          evidence.withdrawalEventMatches then
        .ok { state with phase := .confirmed }
      else .error "Confirmation requires a successful receipt and exact chain events."

/-- The policy intentionally offers no transition from `unknown` to `fresh`. -/
def retryAllowed (state : Attempt) : Bool :=
  match state.phase with
  | .fresh => true
  | _ => false

end Tornado.Policy
