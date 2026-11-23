import Tornado.Cli.SmartAccountStatus

namespace Tornado.Cli.SmartAccountStatus.Test

open Lean Tornado.Domain Tornado.Crypto Tornado.Runtime
open Tornado.Cli.SmartAccountStatus

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def rejected (value : Except String α) (message : String) : IO Unit := do
  if value.isOk then throw <| IO.userError message

private def ownerText : String := "0x0000000000000000000000000000000000000001"
private def accountText : String := "0x0000000000000000000000000000000000000002"
private def recipientText : String := "0x0000000000000000000000000000000000000003"
private def hashText : String :=
  "0x" ++ String.ofList (List.replicate 64 '1')
private def blockHashText : String :=
  "0x" ++ String.ofList (List.replicate 64 '2')
private def calldataHashText : String :=
  "0x" ++ bytesToHex (keccak256 ByteArray.empty)

private def journalJson (chain : Nat := 1) : Json := Json.mkObj [
  ("version", toJson (1 : Nat)), ("kind", toJson ("smart-account-recovery" : String)),
  ("chainId", toJson chain), ("owner", toJson ownerText),
  ("account", toJson accountText), ("recipient", toJson recipientText),
  ("transactionHash", toJson hashText), ("calldataHash", toJson calldataHashText),
  ("status", toJson ("prepared" : String))]

private def transactionJson (owner : String := ownerText)
    (input : String := "0x") (chain : String := "0x1")
    (blockHash : Json := toJson blockHashText)
    (blockNumber : Json := toJson ("0x10" : String))
    (transactionIndex : Json := toJson ("0x0" : String))
    (value : String := "0x0") (kind : String := "0x2") : Json := Json.mkObj [
  ("hash", toJson hashText), ("from", toJson owner),
  ("to", toJson accountText), ("input", toJson input),
  ("chainId", toJson chain), ("value", toJson value), ("type", toJson kind),
  ("blockHash", blockHash),
  ("blockNumber", blockNumber), ("transactionIndex", transactionIndex)]

private def receiptJson (status : String := "0x1")
    (owner : String := ownerText) : Json := Json.mkObj [
  ("transactionHash", toJson hashText), ("blockHash", toJson blockHashText),
  ("blockNumber", toJson ("0x10" : String)),
  ("transactionIndex", toJson ("0x0" : String)),
  ("from", toJson owner), ("to", toJson accountText),
  ("status", toJson status), ("logs", Json.arr #[])]

def main : IO UInt32 := do
  try
    let journal ← unwrap (parseJournal journalJson.compress)
    require (journal.chainId == .mainnet && journal.owner == 1 &&
      journal.account == 2 && journal.recipient == 3)
      "Recovery journal lost selected identities."
    rejected (parseJournal (journalJson 2).compress)
      "Unsupported recovery chain was accepted."
    rejected (parseJournal "{}") "Missing recovery fields were accepted."
    let transaction := transactionJson
    let receipt := receiptJson
    require ((observe journal transaction receipt).status == .confirmed)
      "Exact recovery transaction and receipt were not confirmed."
    require ((observe journal transaction (receiptJson "0x0")).status == .failed)
      "Reverted recovery receipt was not reported failed."
    require ((observe journal transaction Json.null).status == .submitted)
      "Pending recovery receipt was not reported submitted."
    require ((observe journal Json.null receipt).status == .unknown)
      "Missing indexed transaction was not uncertain."
    require ((observe journal (transactionJson recipientText) receipt).status == .unknown)
      "Wrong transaction sender was confirmed."
    require ((observe journal (transactionJson ownerText "0x01") receipt).status == .unknown)
      "Changed calldata was confirmed."
    require ((observe journal (transactionJson ownerText "0x" "0xaa") receipt).status == .unknown)
      "Wrong transaction chain was confirmed."
    require ((observe journal (transactionJson (value := "0x1")) receipt).status == .unknown)
      "A value-bearing recovery transaction was confirmed."
    require ((observe journal (transactionJson (kind := "0x4")) receipt).status == .unknown)
      "An unexpected recovery transaction type was confirmed."
    require ((observe journal transaction (receiptJson "0x1" recipientText)).status == .unknown)
      "Wrong receipt sender was confirmed."
    require ((observe journal (transactionJson (blockHash := Json.null)) receipt).status == .unknown)
      "Pending transaction was confirmed using a stale receipt."
    require ((observe journal (transactionJson (blockNumber := toJson ("0x11" : String))) receipt).status == .unknown)
      "Transaction and receipt block numbers disagreed but were confirmed."
    require ((observe journal (transactionJson (transactionIndex := toJson ("0x1" : String))) receipt).status == .unknown)
      "Transaction and receipt indexes disagreed but were confirmed."
    require ((observe journal (transactionJson (blockHash := toJson hashText)) receipt).status == .unknown)
      "Transaction and receipt block hashes disagreed but were confirmed."
    require ((observe journal (transactionJson (blockHash := Json.null)) Json.null).status == .submitted)
      "Pending transaction without a receipt was not reported submitted."
    require ((observe journal transaction (Json.mkObj [])).status == .unknown)
      "Malformed receipt was confirmed."
    require ((render journal (observe journal transaction receipt)).startsWith "Status: confirmed\nTransaction: ")
      "Recovery status rendering changed."
    let fetch : JsonRpc.Method → Array Json → IO Json := fun method _ =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .getTransactionByHash => pure transaction
      | .getTransactionReceipt => pure receipt
      | _ => throw <| IO.userError "Unexpected RPC method."
    require ((← inspectWith journal fetch).status == .confirmed)
      "Offline read-only status adapter did not confirm exact evidence."
    let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method _ =>
      match method with
      | .chainId => pure (toJson ("0xaa" : String))
      | _ => throw <| IO.userError "Network check did not run first."
    let mut rejectedChain := false
    try
      let _ ← inspectWith journal wrongChain
      pure ()
    catch _ => rejectedChain := true
    require rejectedChain "Wrong RPC chain was accepted."
    IO.println "PASS: recovery journal, zero-value typed transaction, receipt, inclusion, and RPC-chain checks"
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end Tornado.Cli.SmartAccountStatus.Test

def main : IO UInt32 := Tornado.Cli.SmartAccountStatus.Test.main
