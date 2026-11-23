import Lean

/-!
Pure safety gate for a multi-note UserOperation. The state machine is executable
Lean, but `reserveNote` models a successful durable write. Actual storage
durability remains an external assumption of the effectful caller.
-/

namespace Tornado.Policy.Batch

inductive Phase where
  | fresh | reviewed | signed | reserving | exposed | submitted | unknown | confirmed
  deriving Repr, BEq, DecidableEq

structure Attempt where
  phase : Phase := .fresh
  selected : List String := []
  reviewedHash : Option String := none
  signedHash : Option String := none
  reserved : List String := []
  sends : Nat := 0
  deriving Repr

structure Evidence where
  receiptSuccess : Bool
  entryPointEventMatches : Bool
  userOpHash : String
  matchedNullifiers : List String
  deriving Repr

inductive Action where
  | prepare (nullifiers : List String) (hash : String)
  | sign (hash : String)
  | reserveNote (nullifier : String)
  | expose
  | send
  | markUnknown
  | confirm (evidence : Evidence)
  deriving Repr

def validSelection (notes : List String) : Bool :=
  !notes.isEmpty && notes.length <= 12 && notes.all (· != "") &&
    notes.eraseDups.length == notes.length

def allReserved (state : Attempt) : Bool :=
  state.selected.all state.reserved.contains

def exactEvents (selected matched : List String) : Bool :=
  matched.length == selected.length && matched.eraseDups.length == matched.length &&
    selected.all matched.contains && matched.all selected.contains

/-- The pure batch transition gate. An effectful implementation must
    attest that every `reserveNote` was durable before calling `expose`. -/
def step (state : Attempt) (action : Action) : Except String Attempt :=
  match action with
  | .prepare notes hash =>
      if state.phase == .fresh && validSelection notes && hash != "" then
        .ok { state with phase := .reviewed, selected := notes, reviewedHash := some hash }
      else .error "A batch must select unique notes and an approved payload."
  | .sign hash =>
      if state.phase == .reviewed && state.reviewedHash == some hash then
        .ok { state with phase := .signed, signedHash := some hash }
      else .error "The batch signature differs from the reviewed payload."
  | .reserveNote note =>
      if (state.phase == .signed || state.phase == .reserving) &&
          state.selected.contains note && !state.reserved.contains note &&
          state.reviewedHash == state.signedHash && state.signedHash.isSome then
        .ok { state with phase := .reserving, reserved := state.reserved ++ [note] }
      else .error "The note is not a fresh reservation for this signed batch."
  | .expose =>
      if state.phase == .reserving && allReserved state &&
          state.reviewedHash == state.signedHash && state.signedHash.isSome then
        .ok { state with phase := .exposed }
      else .error "Every selected note must be reserved before exposure."
  | .send =>
      if state.phase == .exposed && allReserved state &&
          state.reviewedHash == state.signedHash && state.signedHash.isSome &&
          state.sends == 0 then
        .ok { state with phase := .submitted, sends := 1 }
      else .error "A reserved batch can be sent only once."
  | .markUnknown =>
      if state.phase == .exposed || state.phase == .submitted then
        .ok { state with phase := .unknown }
      else .error "Only an exposed or submitted batch can become unknown."
  | .confirm evidence =>
      if (state.phase == .exposed || state.phase == .submitted || state.phase == .unknown) &&
          evidence.receiptSuccess && evidence.entryPointEventMatches &&
          state.signedHash == some evidence.userOpHash &&
          exactEvents state.selected evidence.matchedNullifiers then
        .ok { state with phase := .confirmed }
      else .error "Confirmation requires a receipt and every exact note event."

def retryAllowed (state : Attempt) : Bool :=
  state.phase == .fresh

end Tornado.Policy.Batch
