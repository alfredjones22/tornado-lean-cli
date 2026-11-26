import Tornado.Runtime.ProtectedTxSender

open Lean Tornado.Protocol Tornado.Runtime
open Tornado.Runtime.ProtectedTxSender

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def bytes (value count : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn fun index : Fin count =>
    UInt8.ofNat (value / 256 ^ (count - 1 - index.val) % 256))

private def original : RpcReceipt.Receipt := {
  transactionHash := bytes 1 32, blockHash := bytes 2 32,
  blockNumber := 100, transactionIndex := 2, origin := 3,
  to := some 4, success := true, logs := [] }

private def receiptJson (receipt : RpcReceipt.Receipt) : Json := Json.mkObj [
  ("transactionHash", toJson (hex receipt.transactionHash)),
  ("blockHash", toJson (hex receipt.blockHash)),
  ("blockNumber", toJson (quantity receipt.blockNumber)),
  ("transactionIndex", toJson (quantity receipt.transactionIndex)),
  ("from", toJson (hex (bytes receipt.origin 20))),
  ("to", match receipt.to with
    | none => Json.null
    | some target => toJson (hex (bytes target 20))),
  ("status", toJson (if receipt.success then "0x1" else "0x0" : String)),
  ("logs", Json.arr #[])]

private def blockJson (number : Nat := original.blockNumber)
    (hash : ByteArray := original.blockHash) : Json := Json.mkObj [
  ("number", toJson (quantity number)), ("hash", toJson (hex hash))]

private structure Observation where
  success : Bool
  pauses : Nat
  heads : Nat
  methods : Array JsonRpc.Method

/-- Every response is public synthetic data. Only the injected pause advances
    the head; this test never sleeps or performs HTTP requests. -/
private def observe (confirmations : Option Nat)
    (block : Json := blockJson) (receipt : Json := receiptJson original)
    (initialHead : Nat := original.blockNumber) : IO Observation := do
  let head ← IO.mkRef initialHead
  let pauses ← IO.mkRef (0 : Nat)
  let heads ← IO.mkRef (0 : Nat)
  let methods ← IO.mkRef (#[] : Array JsonRpc.Method)
  let fetch (_id : Nat) (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    methods.modify (·.push method)
    match method with
    | .blockNumber =>
      require params.isEmpty "Head query unexpectedly contained parameters."
      heads.modify (· + 1)
      return toJson (quantity (← head.get))
    | .getBlockByNumber =>
      require (params == #[toJson (quantity original.blockNumber), toJson false])
        "Confirmation queried a future block instead of the original inclusion block."
      return block
    | .getTransactionReceipt =>
      require (params == #[toJson (hex original.transactionHash)])
        "Confirmation queried a different transaction receipt."
      return receipt
    | _ => throw <| IO.userError "Unexpected confirmation RPC method."
  let pause : IO Unit := do
    pauses.modify (· + 1)
    head.modify (· + 1)
  let success ← try
    match confirmations with
    | none => waitReceiptDepthWith fetch pause original
    | some count => waitReceiptDepthWith fetch pause original count
    pure true
  catch _ => pure false
  return ⟨success, ← pauses.get, ← heads.get, ← methods.get⟩

def main : IO UInt32 := do
  let included ← observe (some 1)
  require (included.success && included.pauses == 0 && included.heads == 1 &&
    included.methods == #[.blockNumber, .getBlockByNumber, .getTransactionReceipt])
    "One confirmation waited beyond the inclusion block or skipped exact block/receipt checks."
  let defaultDepth ← observe none
  require (defaultDepth.success && defaultDepth.pauses == 0 && defaultDepth.heads == 1 &&
    defaultDepth.methods == #[.blockNumber, .getBlockByNumber, .getTransactionReceipt])
    "The default confirmation policy waited beyond one inclusion or skipped exact evidence checks."
  let beforeInclusion ← observe none blockJson (receiptJson original) (original.blockNumber - 1)
  require (beforeInclusion.success && beforeInclusion.pauses == 1 && beforeInclusion.heads == 2 &&
    beforeInclusion.methods == #[.blockNumber, .blockNumber, .getBlockByNumber, .getTransactionReceipt])
    "The single-inclusion default advanced before the inclusion block was observed."
  for changedBlock in [blockJson (original.blockNumber + 1),
      blockJson original.blockNumber (bytes 5 32), Json.null] do
    let observed ← observe (some 1) changedBlock
    require (!observed.success && observed.pauses == 0 && observed.heads == 1 &&
      observed.methods == #[.blockNumber, .getBlockByNumber])
      "One confirmation accepted changed or disappeared inclusion-block evidence."
  for changedReceipt in [
      receiptJson { original with transactionHash := bytes 9 32 },
      receiptJson { original with blockHash := bytes 9 32 },
      receiptJson { original with blockNumber := original.blockNumber + 1 },
      receiptJson { original with transactionIndex := original.transactionIndex + 1 },
      receiptJson { original with origin := original.origin + 1 },
      receiptJson { original with to := some 9 },
      receiptJson { original with to := none },
      receiptJson { original with success := false }, Json.null] do
    let observed ← observe (some 1) blockJson changedReceipt
    require (!observed.success && observed.pauses == 0 && observed.heads == 1 &&
      observed.methods == #[.blockNumber, .getBlockByNumber, .getTransactionReceipt])
      "One confirmation accepted a changed or disappeared exact receipt."
  for count in [0, 181] do
    let invalid ← observe (some count)
    require (!invalid.success && invalid.pauses == 0 && invalid.heads == 0 && invalid.methods.isEmpty)
      "An invalid confirmation count performed RPC or pause effects."
  IO.println "PASS: single-inclusion default, exact block/receipt stability, and bounded RPC-free rejection"
  return 0
