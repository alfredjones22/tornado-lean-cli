import Tornado.Policy.EvidenceBridge

/-!
An abstract one-note command driver with an explicit external-effect log.
`DurableAck` and `authenticate` are interfaces to effectful adapters, not
implementations of protected files or an RPC client. The driver admits their
results only after the native policy and strict event bridge agree.
-/

namespace Tornado.Spec.Effects

open Tornado.Policy
open Tornado.Protocol.Events

structure Config where
  chainId : Nat
  entry : ExpectedEntry
  withdrawal : ExpectedWithdrawal

/-- An IO adapter may return this only after its reservation is durable. The
    Bool is checked by the driver; its truthfulness is a trusted boundary. -/
structure DurableAck where
  candidateHash : String
  durable : Bool

/-- The adapter reports chain and transaction identity with the receipt. An
    external authenticator must bind these fields and logs to chain data. -/
structure Receipt where
  chainId : Nat
  transactionHash : String
  success : Bool
  logs : List Log

inductive Effect where
  | durableReservation (hash : String)
  | signedExposure (hash : String)
  | send (hash : String)
  | uncertain (hash : String)
  | authenticatedConfirmation (hash txHash : String)
  deriving BEq, DecidableEq, Repr

structure State where
  policy : Attempt := {}
  acknowledged : Option String := none
  effects : List Effect := []

inductive Action where
  | review (hash : String)
  | sign (hash : String)
  | reserve (ack : DurableAck)
  | expose
  | send
  | markUnknown
  | confirm (receipt : Receipt)

/-- The only path through this skeleton to a signed exposure requires an
    accepted durable reservation acknowledgment for the signed hash. A real
    adapter must supply the acknowledgment after fsync and directory sync. -/
def step (config : Config) (authenticate : Receipt → Bool)
    (state : State) (action : Action) : Except String State :=
  match action with
  | .review hash =>
      if hash != EvidenceBridge.hashText config.entry.userOpHash then
        .error "Review does not match the configured UserOperation."
      else match stepAttempt state.policy (.approve hash) with
        | .ok policy => .ok { state with policy := policy }
        | .error error => .error error
  | .sign hash =>
      match stepAttempt state.policy (.sign hash) with
      | .ok policy => .ok { state with policy := policy }
      | .error error => .error error
  | .reserve ack =>
      if !ack.durable || state.policy.signedHash != some (ack.candidateHash) then
        .error "A durable reservation for the signed operation is required."
      else match stepAttempt state.policy .reserve with
        | .ok policy => .ok { state with policy := policy, acknowledged := some (ack.candidateHash), effects := state.effects ++ [.durableReservation ack.candidateHash] }
        | .error error => .error error
  | .expose =>
      if !state.acknowledged.isSome || state.acknowledged != state.policy.signedHash then
        .error "Exposure requires an acknowledged durable reservation."
      else match state.acknowledged with
        | none => .error "Exposure requires an acknowledged durable reservation."
        | some hash =>
          match stepAttempt state.policy .expose with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.signedExposure hash] }
          | .error error => .error error
  | .send =>
      if !state.acknowledged.isSome || state.acknowledged != state.policy.signedHash then
        .error "Submission requires an acknowledged durable reservation."
      else match state.acknowledged with
        | none => .error "Submission requires an acknowledged durable reservation."
        | some hash =>
          match stepAttempt state.policy .send with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.send hash] }
          | .error error => .error error
  | .markUnknown =>
      match state.acknowledged with
      | none => .error "Unknown operation has no durable reservation."
      | some hash =>
        match stepAttempt state.policy .markUnknown with
        | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.uncertain hash] }
        | .error error => .error error
  | .confirm receipt =>
      if !authenticate receipt || receipt.chainId != config.chainId ||
          receipt.transactionHash == "" then
        .error "Receipt is not authenticated for the selected chain."
      else if !state.acknowledged.isSome || state.acknowledged != state.policy.signedHash then
        .error "Confirmation has no matching durable reservation."
      else match state.acknowledged with
        | none => .error "Confirmation has no matching durable reservation."
        | some hash =>
          match EvidenceBridge.confirmDirect state.policy receipt.success receipt.logs
            config.entry config.withdrawal with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.authenticatedConfirmation hash receipt.transactionHash] }
          | .error error => .error error

namespace Batch

/-- The reviewed batch identity includes exactly the expected pool withdrawal
    list. Each selected nullifier is rendered to the policy's canonical text. -/
structure Config where
  chainId : Nat
  entry : ExpectedEntry
  withdrawals : List ExpectedWithdrawal

structure DurableAck where
  nullifier : String
  operationHash : String
  durable : Bool

structure State where
  policy : Tornado.Policy.Batch.Attempt := {}
  acknowledged : List String := []
  effects : List Effect := []

inductive Action where
  | prepare (nullifiers : List String) (hash : String)
  | sign (hash : String)
  | reserve (ack : DurableAck)
  | expose
  | send
  | markUnknown
  | confirm (receipt : Receipt)

/-- A pure batch command driver. The caller-supplied durable acknowledgments
    and authenticator are explicit external trust boundaries. -/
def step (config : Config) (authenticate : Receipt → Bool)
    (state : State) (action : Action) : Except String State :=
  match action with
  | .prepare nullifiers hash =>
      if hash != EvidenceBridge.hashText config.entry.userOpHash ||
          nullifiers != EvidenceBridge.withdrawalTexts config.withdrawals then
        .error "Batch review differs from configured withdrawals."
      else match Tornado.Policy.Batch.step state.policy (.prepare nullifiers hash) with
        | .ok policy => .ok { state with policy := policy }
        | .error error => .error error
  | .sign hash =>
      match Tornado.Policy.Batch.step state.policy (.sign hash) with
      | .ok policy => .ok { state with policy := policy }
      | .error error => .error error
  | .reserve ack =>
      if !ack.durable || state.policy.signedHash != some ack.operationHash ||
          !state.policy.selected.contains ack.nullifier then
        .error "Each selected note needs a durable reservation for this batch."
      else match Tornado.Policy.Batch.step state.policy (.reserveNote ack.nullifier) with
        | .ok policy => .ok { state with policy := policy, acknowledged := state.acknowledged ++ [ack.nullifier], effects := state.effects ++ [.durableReservation ack.nullifier] }
        | .error error => .error error
  | .expose =>
      if !state.policy.selected.all state.acknowledged.contains ||
          state.policy.signedHash.isNone then
        .error "Every selected note needs a durable reservation before exposure."
      else match state.policy.signedHash with
        | none => .error "Batch signed hash is absent."
        | some hash =>
          match Tornado.Policy.Batch.step state.policy .expose with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.signedExposure hash] }
          | .error error => .error error
  | .send =>
      if !state.policy.selected.all state.acknowledged.contains ||
          state.policy.signedHash.isNone then
        .error "Batch submission requires every durable reservation."
      else match state.policy.signedHash with
        | none => .error "Batch signed hash is absent."
        | some hash =>
          match Tornado.Policy.Batch.step state.policy .send with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.send hash] }
          | .error error => .error error
  | .markUnknown =>
      match state.policy.signedHash with
      | none => .error "Unknown batch has no signed operation."
      | some hash =>
        match Tornado.Policy.Batch.step state.policy .markUnknown with
        | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.uncertain hash] }
        | .error error => .error error
  | .confirm receipt =>
      if !authenticate receipt || receipt.chainId != config.chainId ||
          receipt.transactionHash == "" then
        .error "Batch receipt is not authenticated for the selected chain."
      else if !state.policy.selected.all state.acknowledged.contains then
        .error "Batch confirmation lacks durable note reservations."
      else match state.policy.signedHash with
        | none => .error "Batch confirmation has no signed operation."
        | some hash =>
          match EvidenceBridge.confirmBatch state.policy receipt.success receipt.logs
            config.entry config.withdrawals with
          | .ok policy => .ok { state with policy := policy, effects := state.effects ++ [.authenticatedConfirmation hash receipt.transactionHash] }
          | .error error => .error error

end Batch

end Tornado.Spec.Effects
