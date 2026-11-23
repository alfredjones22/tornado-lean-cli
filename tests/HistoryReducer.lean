import Lean
import Tornado.Protocol.HistoryReducer

namespace Tornado.Protocol.HistoryReducer.Test

open Lean Tornado.Protocol.Events Tornado.Protocol.SagaHistory
open Tornado.Protocol.RpcHistory Tornado.Protocol.HistoryReducer

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"{name}: assertion failed")

private def success (name : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"{name}: {error}")

private def failure (name : String) (value : Except String α) : IO Unit :=
  match value with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error _ => pure ()

private def word (value : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:32] do
    out := out.push (UInt8.ofNat ((value / 256 ^ (31 - i)) % 256))
  return out

private def deposit (block log leaf commitment : Nat) : ValidatedEvent :=
  { blockNumber := block, logIndex := log, isDeposit := true,
    log := { address := 170, topics := #[depositTopic, word commitment],
             data := word leaf ++ word 123 } }

private def withdrawal (block log nullifier : Nat) : ValidatedEvent :=
  { blockNumber := block, logIndex := log, isDeposit := false,
    log := { address := 170, topics := #[withdrawalTopic, word 187],
             data := word 204 ++ word nullifier ++ word 3 } }

private def readRoot (index : Nat) : IO Nat := do
  let raw ← IO.FS.readFile "fixtures/history-reducer-vectors.json"
  let fixture ← success "root fixture parse" (Json.parse raw)
  let rows ← success "root rows" ((← success "roots" (fixture.getObjVal? "roots")).getArr?)
  let row ← match rows[index]? with
    | some value => pure value
    | none => throw (IO.userError "Root fixture row missing")
  let decimal ← success "root decimal" ((← success "root" (row.getObjVal? "root")).getStr?)
  match decimal.toNat? with
  | some value => pure value
  | none => throw (IO.userError "Root fixture is not decimal")

def main : IO Unit := do
  let root0 ← readRoot 0
  let root1 ← readRoot 1
  let root12 ← readRoot 2
  let root13 ← readRoot 3
  let root123 ← readRoot 4
  let fresh ← success "fresh selected pool" (emptyState 1 170 100)
  let _ ← success "fresh state shape" (validateState fresh)
  let first : Batch := { chainId := 1, pool := 170,
                         fromBlock := 100, toBlock := 101, capturedHead := 102,
                         finalizedHead := 101, onchainClaimBlock := 101,
                         onchainLeafCount := 2, onchainRoot := root12,
                         events := #[deposit 100 0 0 1, deposit 101 0 1 2,
                           withdrawal 101 1 55] }
  let state ← success "two leaves and spent nullifier" (applyBatch fresh first)
  require "same-block root/count/cursor" (state.lastSyncedBlock == 101 &&
    state.deposits.size == 2 && state.verifiedRoot == some root12 &&
    state.finalizedBlock == some 101)
  require "spent nullifier recorded" (state.withdrawals.size == 1 &&
    state.withdrawals[0]!.nullifierHash == word 55)
  require "result postcondition" (resultBound fresh first state)
  let selection : Selection := { chainId := 1, pool := 170,
                                 registeredBlock := 100, lastSyncedBlock := 99, head := 102 }
  let history : ValidatedHistory := { replayStart := 100, coverage := 101,
                                      events := first.events }
  let viaSaga ← success "Saga adapter" (applySaga fresh selection history 101 101 2 root12)
  require "Saga adapter equivalence" (viaSaga.deposits.size == state.deposits.size &&
    viaSaga.verifiedRoot == state.verifiedRoot)
  failure "Saga mismatched claim block" (applySaga fresh selection history 101 102 2 root12)
  let rpcSelection := { selection with lastSyncedBlock := 101 }
  let emptyTail : CheckedSlice := { fromBlock := 102, toBlock := 102, events := #[] }
  let viaRpc ← success "RPC tail adapter" (applyRpc state rpcSelection emptyTail 101 102 2 root12)
  require "RPC tail cursor" (viaRpc.lastSyncedBlock == 102 && viaRpc.deposits.size == 2)
  failure "RPC adapter stale selection cursor" (applyRpc state selection emptyTail 101 102 2 root12)

  let reorg : Batch := { first with fromBlock := 101, toBlock := 102, onchainClaimBlock := 102, onchainRoot := root13, events := #[deposit 101 0 1 3, withdrawal 102 0 66] }
  let replaced ← success "rewind and replacement" (applyBatch state reorg)
  require "reorg prunes replaced events" (replaced.deposits.size == 2 &&
    replaced.deposits[1]!.commitment == word 3 &&
    replaced.withdrawals.size == 1 &&
    replaced.withdrawals[0]!.nullifierHash == word 66)

  let empty : Batch := { first with toBlock := 100, onchainClaimBlock := 100, onchainLeafCount := 0, onchainRoot := root0, events := #[], finalizedHead := 99 }
  let emptyStateResult ← success "empty pool range" (applyBatch fresh empty)
  require "stale finalized head is not promoted" (emptyStateResult.finalizedBlock == none)
  let single : Batch := { empty with events := #[deposit 100 0 0 1], onchainLeafCount := 1, onchainRoot := root1 }
  let one ← success "one pinned SDK root" (applyBatch fresh single)
  require "single leaf root" (one.verifiedRoot == some root1)
  let three : Batch := { first with toBlock := 102, onchainClaimBlock := 102, onchainLeafCount := 3, onchainRoot := root123, events := #[deposit 100 0 0 1, deposit 101 0 1 2, deposit 102 0 2 3] }
  let third ← success "three pinned SDK leaves" (applyBatch fresh three)
  require "three leaf root" (third.verifiedRoot == some root123)

  failure "wrong pool" (applyBatch fresh { first with pool := 171 })
  failure "wrong chain" (applyBatch fresh { first with chainId := 11155111 })
  failure "gap after cursor" (applyBatch fresh { first with fromBlock := 101 })
  failure "range behind saved cursor" (applyBatch state { first with toBlock := 100, onchainClaimBlock := 100 })
  failure "range beyond captured head" (applyBatch fresh { first with capturedHead := 100 })
  failure "mismatched claim block" (applyBatch fresh { first with onchainClaimBlock := 102 })
  failure "mismatched leaf count" (applyBatch fresh { first with onchainLeafCount := 1 })
  failure "mismatched Merkle root" (applyBatch fresh { first with onchainRoot := root13 })
  failure "missing first leaf" (applyBatch fresh { first with events := #[deposit 100 0 1 1, deposit 101 0 2 2] })
  failure "duplicate leaf index" (applyBatch fresh { first with events := #[deposit 100 0 0 1, deposit 101 0 0 2] })
  failure "duplicate commitment" (applyBatch fresh { first with events := #[deposit 100 0 0 1, deposit 101 0 1 1] })
  failure "duplicate nullifier" (applyBatch fresh { first with events := #[deposit 100 0 0 1, deposit 101 0 1 2, withdrawal 101 1 55, withdrawal 101 2 55] })
  failure "out of order" (applyBatch fresh { first with events := #[deposit 101 0 0 1, deposit 100 0 1 2] })
  let wrongEmitter := { deposit 100 0 0 1 with log := { (deposit 100 0 0 1).log with address := 171 } }
  failure "event wrong emitting pool" (applyBatch fresh { first with events := #[wrongEmitter] })
  failure "event outside range" (applyBatch fresh { first with events := #[deposit 99 0 0 1, deposit 101 0 1 2] })
  let malformed := { deposit 100 0 0 1 with log := { (deposit 100 0 0 1).log with data := word 0 } }
  failure "malformed deposit log" (applyBatch fresh { first with events := #[malformed] })
  failure "replay before finality" (applyBatch state { first with fromBlock := 100 })
  failure "regressed finality" (applyBatch state { reorg with finalizedHead := 100 })
  let corrupt := { state with deposits := state.deposits.set! 0 { state.deposits[0]! with leafIndex := 1 } }
  failure "corrupt cached leaf order" (applyBatch corrupt reorg)
  IO.println "PASS: pinned SDK roots, selected-pool replay, reorg pruning, and rejection gates"

end Tornado.Protocol.HistoryReducer.Test

def main : IO Unit := Tornado.Protocol.HistoryReducer.Test.main
