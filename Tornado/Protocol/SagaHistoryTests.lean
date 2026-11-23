import Tornado.Protocol.SagaHistory

namespace Tornado.Protocol.SagaHistoryTests

open Tornado.Protocol.SagaHistory

private def read (name : String) : IO ByteArray := do
  let root := (← IO.getEnv "TORNADO_SAGA_FIXTURES").getD "fixtures/saga-history/"
  IO.FS.readBinFile (root ++ name)

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"{name}: assertion failed"

private def success (name : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{name}: {message}"

private def failure (name : String) (value : Except String α) : IO Unit :=
  match value with
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly accepted"
  | .error _ => pure ()

def main : IO Unit := do
  let selection : Selection := {
    chainId := 1, pool := 170, registeredBlock := 100,
    lastSyncedBlock := 103, finalizedBlock := some 102, head := 108 }
  require "rewind" (firstReplayBlock selection == 102)
  require "legacy rewind floor" (firstReplayBlock
    { selection with finalizedBlock := none } == 100)
  failure "snapshot cursor beyond head" (planIndex
    { selection with lastSyncedBlock := 109 } (← read "valid-index.json"))
  failure "registration beyond cursor" (planIndex
    { selection with registeredBlock := 105 } (← read "valid-index.json"))
  let fresh ← success "fresh cursor one before registration" <| planIndex
    { selection with lastSyncedBlock := 99, finalizedBlock := none }
    (← read "valid-index.json")
  require "fresh cursor starts at registration" (fresh.replayStart == 100)
  require "segment budget accepts limit" (withinSegmentBudget maxSelectedSegments)
  require "segment budget rejects excess" (!withinSegmentBudget (maxSelectedSegments + 1))
  require "byte budget accepts limit" (withinByteSizeBudget
    #[maxAggregateCompressedBytes - 1, 1])
  require "byte budget rejects excess" (!withinByteSizeBudget
    #[maxAggregateCompressedBytes, 1])
  let plan ← success "valid index" <| planIndex selection (← read "valid-index.json")
  require "coverage" (plan.coverage == 108 && plan.replayStart == 102 && plan.segments.size == 2)
  let c0 ← read "chunk0.jsonl.gz"
  let c1 ← read "chunk1.jsonl.gz"
  let history ← success "valid chunks" <| validateChunks plan #[c0, c1]
  require "two selected events" (history.events.size == 2)
  let rawHistory ← success "HTTP already decoded gzip" <|
    validateChunks plan #[← read "chunk0.jsonl", ← read "chunk1.jsonl"]
  require "raw payload parity" (rawHistory.events.size == history.events.size &&
    rawHistory.coverage == history.coverage)
  let narrow ← success "narrow range" <| admitRange history 106 108
  require "narrow event" (narrow.size == 1 && !narrow[0]!.isDeposit)
  failure "range before rewind" (admitRange history 101 108)
  failure "range past coverage" (admitRange history 102 109)
  failure "inverted range" (admitRange history 106 105)
  failure "missing chunk" (validateChunks plan #[c0])
  for name in #["gap-index.json", "overlap-index.json", "wrong-chain-index.json",
      "duplicate-index.json", "traversal-index.json"] do
    failure name (planIndex selection (← read name))
  let wrongDigest ← success "wrong digest manifest" <|
    planIndex selection (← read "wrong-digest-index.json")
  failure "wrong checksum" (validateChunks wrongDigest #[c0, c1])
  let order ← success "order manifest" <|
    planIndex selection (← read "out-of-order-index.json")
  failure "out of order" (validateChunks order #[← read "out-of-order.jsonl.gz", c1])
  let pool ← success "pool manifest" <|
    planIndex selection (← read "wrong-pool-index.json")
  failure "untracked pool" (validateChunks pool #[← read "wrong-pool.jsonl.gz", c1])
  let topic ← success "topic manifest" <|
    planIndex selection (← read "wrong-topic-index.json")
  failure "event topic mismatch" (validateChunks topic #[← read "wrong-topic.jsonl.gz", c1])
  let short ← success "short manifest" <|
    planIndex selection (← read "short-index.json")
  require "partial coverage recorded" (short.coverage == 104)
  failure "partial history not fresh" (assertPoolFreshness selection
    { chainId := 1, pool := 170, lastSyncedBlock := short.coverage })
  let _ ← success "fresh pool" <| assertPoolFreshness selection
    { chainId := 1, pool := 170, lastSyncedBlock := 108 }
  failure "stale pool" (assertPoolFreshness selection
    { chainId := 1, pool := 170, lastSyncedBlock := 107 })
  failure "wrong chain" (assertPoolFreshness selection
    { chainId := 11155111, pool := 170, lastSyncedBlock := 108 })
  failure "wrong pool" (assertPoolFreshness selection
    { chainId := 1, pool := 171, lastSyncedBlock := 108 })
  IO.println "Saga history: 34 offline fixture assertions passed"

end Tornado.Protocol.SagaHistoryTests

def main : IO Unit := Tornado.Protocol.SagaHistoryTests.main
