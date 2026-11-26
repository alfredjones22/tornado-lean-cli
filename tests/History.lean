import Tornado.Cli.History
import Tornado.Cli.WithdrawalSession

namespace Tornado.Cli.History.Test

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime

private def require (label : String) (value : Bool) : IO Unit :=
  unless value do throw <| IO.userError s!"{label}: assertion failed"

private def checked (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def expectFailure (label : String) (action : IO α) : IO Unit := do
  let rejected ← try
      let _ ← action
      pure false
    catch _ => pure true
  require label rejected

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push (UInt8.ofNat ((value / 256 ^ (31 - i)) % 256))
  return bytes

private def wordHex (value : Nat) : String :=
  "0x" ++ bytesToHex (word value)

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def envelope (id : Nat) (value : Json) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("result", value)]).compress

private def errorEnvelope (id : Nat) (message : String) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("error", Json.mkObj [
      ("code", toJson (-32000 : Int)), ("message", toJson message)])]).compress

private def getString (json : Json) (name : String) : IO String := do
  checked name ((← checked name (json.getObjVal? name)).getStr?)

private def parsedQuantity (json : Json) (name : String) : IO Nat := do
  checked name (JsonRpc.parseHexQuantity (← getString json name))

private def fixtureNote : String :=
  "tornado-eth-0.01-1-0x33567fb6463d588b0ef7ff2d415130e0d91059781005f504671ddc3f03c4adc8b873cfa627a16e46d1f33b81d9c7e86772a083575ccccb9104ed77057b53"

private def secondFixtureNote : String :=
  "tornado-eth-1-1-0x38ba0d601404fd62799e1f48f412425062db944406ad748338cdf17cc91e1b0e52370aca05d3731e2f6e278d0fb871ecedf5a9de9a20969a636b16acde90"

private def poolAddress : String := "0x199112Eb461ea7eeC1D75B33343542e1d069B41c"
private def poolBlock : Nat := 26198980
private def blockHash : String := wordHex 8
private def transactionHash : String := wordHex 7
private def sender : String := "0x00000000000000000000000000000000000000aa"

private def depositLog (commitment : String) : Json :=
  Json.mkObj [
    ("address", toJson poolAddress), ("blockNumber", toJson (quantityHex poolBlock)),
    ("logIndex", toJson ("0x0" : String)), ("transactionIndex", toJson ("0x0" : String)),
    ("transactionHash", toJson transactionHash), ("blockHash", toJson blockHash),
    ("topics", toJson #["0x" ++ bytesToHex Events.depositTopic, commitment]),
    ("data", toJson ("0x" ++ bytesToHex (word 0) ++ bytesToHex (word 123))),
    ("removed", toJson false)]

private def withdrawalLog (nullifierHash : String) : Json :=
  Json.mkObj [
    ("address", toJson poolAddress), ("blockNumber", toJson (quantityHex poolBlock)),
    ("logIndex", toJson ("0x1" : String)), ("transactionIndex", toJson ("0x0" : String)),
    ("transactionHash", toJson transactionHash), ("blockHash", toJson blockHash),
    ("topics", toJson #["0x" ++ bytesToHex Events.withdrawalTopic, wordHex 0xbb]),
    ("data", toJson ("0x" ++ bytesToHex (word 0xcc) ++
      String.ofList (nullifierHash.toList.drop 2) ++ bytesToHex (word 3))),
    ("removed", toJson false)]

private def receipt (logs : Array Json) (reverted : Bool) : Json :=
  Json.mkObj [
    ("transactionHash", toJson transactionHash), ("blockHash", toJson blockHash),
    ("blockNumber", toJson (quantityHex poolBlock)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson sender), ("to", toJson poolAddress),
    ("status", toJson (if reverted then "0x0" else "0x1")),
    ("logs", Json.arr logs)]

private structure Config where
  omitLog : Bool := false
  spentMismatch : Bool := false
  revertedReceipt : Bool := false
  changedBlockHash : Bool := false
  wrongChain : Bool := false
  withWithdrawal : Bool := false
  echoNullifierError : Bool := false
  knownRoot : Bool := true
  advancedPool : Bool := false
  secondNote : Option BackupIdentity := none
  deriving Inhabited

private def mock (note : BackupIdentity) (config : Config) : IO HistorySync.Transport := do
  let commitment ← checked "commitment" (parseHexBytes note.publicIdentity.commitment)
  let commitmentValue := commitment.data.foldl (fun value byte => value * 256 + byte.toNat) 0
  let mut leaves := #[commitmentValue]
  if let some second := config.secondNote then
    let bytes ← checked "second commitment" (parseHexBytes second.publicIdentity.commitment)
    leaves := leaves.push (bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0)
  let tree ← checked "tree" (buildMimcTree leaves)
  let log := depositLog note.publicIdentity.commitment
  let mut allLogs := if config.withWithdrawal then
    #[log, withdrawalLog note.publicIdentity.nullifierHash] else #[log]
  if let some second := config.secondNote then
    let secondLog := ((depositLog second.publicIdentity.commitment).setObjVal!
      "logIndex" (toJson ("0x1" : String))).setObjVal! "data"
      (toJson ("0x" ++ bytesToHex (word 1) ++ bytesToHex (word 123)))
    allLogs := allLogs.push secondLog
  let headerCalls ← IO.mkRef 0
  return {
    sagaIndex := throw <| IO.userError "offline fixture has no Saga index"
    sagaChunk := fun _ => throw <| IO.userError "unexpected Saga chunk"
    rpc := fun id method params => do
      match method with
      | .chainId =>
        return envelope id (toJson (if config.wrongChain then "0xaa36a7" else "0x1"))
      | .blockNumber => return envelope id (toJson
          (quantityHex (poolBlock + if config.advancedPool then 1 else 0)))
      | .call =>
        let call ← match params[0]? with
          | some value => pure value | none => throw <| IO.userError "missing eth_call"
        let data ← getString call "data"
        let block ← match params[1]? with
          | some value => checked "call block" (JsonRpc.parseHexQuantity
              (← checked "call block" value.getStr?))
          | none => throw <| IO.userError "missing call block"
        require "exact block eth_call"
          (block == poolBlock + if config.advancedPool then 1 else 0)
        if data == "0x" ++ bytesToHex (Abi.selector "nextIndex()") then
          return envelope id (toJson (wordHex (leaves.size + if config.advancedPool then 1 else 0)))
        if data == "0x" ++ bytesToHex (Abi.selector "getLastRoot()") then
          return envelope id (toJson (wordHex (tree.root + if config.advancedPool then 1 else 0)))
        if data == "0x" ++ bytesToHex (Abi.selector "isKnownRoot(bytes32)" ++ word tree.root) then
          return envelope id (toJson (wordHex (if config.knownRoot then 1 else 0)))
        if data == "0x" ++ bytesToHex (Abi.selector "isSpent(bytes32)") ++
            String.ofList (note.publicIdentity.nullifierHash.toList.drop 2) ||
            config.secondNote.any (fun second => data == "0x" ++
              bytesToHex (Abi.selector "isSpent(bytes32)") ++
              String.ofList (second.publicIdentity.nullifierHash.toList.drop 2)) then
          if config.echoNullifierError then
            return errorEnvelope id ("RPC rejected " ++ note.publicIdentity.nullifierHash)
          return envelope id (toJson (wordHex (if config.spentMismatch || config.withWithdrawal then 1 else 0)))
        throw <| IO.userError "unexpected eth_call selector"
      | .getLogs =>
        let filter ← match params[0]? with
          | some value => pure value | none => throw <| IO.userError "missing log filter"
        let fromBlock ← parsedQuantity filter "fromBlock"
        let toBlock ← parsedQuantity filter "toBlock"
        require "only selected pool log filter" ((← getString filter "address").toLower == poolAddress.toLower)
        require "no secret-derived log topic filter" (!(filter.getObjVal? "topics").isOk)
        require "one exact pool block" (fromBlock == poolBlock && toBlock == poolBlock)
        return envelope id (Json.arr (if config.omitLog then #[] else allLogs))
      | .getTransactionReceipt =>
        let hash ← match params[0]? with
          | some value => checked "receipt hash" value.getStr?
          | none => throw <| IO.userError "missing receipt hash"
        require "exact receipt hash" (hash == transactionHash)
        return envelope id (receipt allLogs config.revertedReceipt)
      | .getBlockByNumber =>
        let requested ← match params[0]? with
          | some value => checked "block request" (JsonRpc.parseHexQuantity
              (← checked "block request" value.getStr?))
          | none => throw <| IO.userError "missing block number"
        require "exact block header"
          (requested == poolBlock || (config.advancedPool && requested == poolBlock + 1))
        let previous ← headerCalls.get
        headerCalls.set (previous + 1)
        let hash := if requested > poolBlock || (config.changedBlockHash && previous > 1)
          then wordHex 9 else blockHash
        return envelope id (Json.mkObj [
          ("number", toJson (quantityHex requested)), ("hash", toJson hash),
          ("timestamp", toJson ("0x7b" : String))])
      | _ => throw <| IO.userError "unexpected RPC method"
    nowMs := pure 0 }

def main : IO Unit := do
  let multiBackup := fixtureNote ++ "\n" ++ secondFixtureNote
  require "multi-note backup requires selection"
    (!(History.selectNote multiBackup .mainnet none).isOk)
  let indexed ← checked "selected second note" (History.selectNote multiBackup .mainnet (some "2"))
  require "one-based note-index selection" (indexed.note.raw == secondFixtureNote)
  require "note-index out of bounds rejected"
    (!(History.selectNote multiBackup .mainnet (some "3")).isOk)
  let note ← checked "backup" (parseDepositBackup fixtureNote .mainnet)
  let selected := note.head!
  let good ← mock selected {}
  let selectedHistory ← History.syncPublic good selected.note.pool
  let missingPublicDeposit ← try
      let _ ← History.inspectPublicFromSynced good selectedHistory (word 42) (word 43)
      pure ""
    catch error => pure error.toString
  require "missing selected deposit has recent-RPC, network and backup guidance"
    (missingPublicDeposit.contains "Deposit not found" &&
      missingPublicDeposit.contains "RPC catch up" && missingPublicDeposit.contains "--chain" &&
      !missingPublicDeposit.contains "unique")
  let natOf (raw : String) : IO Nat := do
    return (← checked "public identity" (parseHexBytes raw)).data.foldl
      (fun n byte => n * 256 + byte.toNat) 0
  let metadata : ProverWorkerWire.Metadata := {
    chainId := 1, pool := ← natOf selected.note.pool.address
    commitment := ← natOf selected.publicIdentity.commitment
    nullifierHash := ← natOf selected.publicIdentity.nullifierHash
    amount := selected.note.pool.amount, denomination := selected.note.pool.denomination
    asset := selected.note.pool.asset.symbol
    statusFileName := "tornado-withdraw-1-" ++ String.ofList (List.replicate 64 'a') ++ ".json" }
  let session ← WithdrawalSession.inspectWith good metadata
  let request ← checked "public session Request20" (WithdrawalSession.requestFor session 1 0 0)
  require "session binds selected public identity and checked root"
    (metadata.matchesRequest request && request.leafIndex == 0 &&
      request.root == session.history.state.verifiedRoot.getD 0 &&
      request.siblings.size == 20 && request.pathIndices.size == 20)
  require "session refuses spent state"
    (!(WithdrawalSession.requestFor { session with spentAtHead := true } 1 0 0).isOk)
  require "session refuses forged leaf"
    (!(WithdrawalSession.requestFor { session with leafIndex := 1 } 1 0 0).isOk)
  let samePoolRaw := "tornado-eth-0.01-1-0x" ++ String.ofList (List.replicate 124 '2')
  let samePoolNote ← checked "same-pool backup" (History.selectNote samePoolRaw .mainnet none)
  let secondMetadata := { metadata with
    commitment := ← natOf samePoolNote.publicIdentity.commitment
    nullifierHash := ← natOf samePoolNote.publicIdentity.nullifierHash
    statusFileName := "tornado-withdraw-1-" ++ String.ofList (List.replicate 64 'b') ++ ".json" }
  let base ← mock selected { secondNote := some samePoolNote }
  let syncCount ← IO.mkRef (0 : Nat)
  let counted := { base with rpc := fun id method params => do
    if method == .blockNumber then syncCount.modify (· + 1)
    base.rpc id method params }
  let shared ← WithdrawalSession.inspectManyWith counted #[metadata, secondMetadata]
  let some firstShared := shared[0]? | throw <| IO.userError "Missing first shared session"
  let some secondShared := shared[1]? | throw <| IO.userError "Missing second shared session"
  require "same-pool batch syncs once"
    ((← syncCount.get) == 1 && shared.size == 2 && firstShared.leafIndex == 0 && secondShared.leafIndex == 1)
  let sharedRequests ← checked "shared-tree requests" (WithdrawalSession.requestsMany shared 1)
  let independent ← shared.mapM fun one => checked "independent path"
    (WithdrawalSession.requestFor one 1 0 0)
  require "shared tree preserves each exact independently reconstructed path"
    (sharedRequests == independent)
  let reversed ← checked "ordered shared paths" (WithdrawalSession.requestsMany shared.reverse 1)
  require "shared preparation preserves selection ordering" (reversed == sharedRequests.reverse)
  require "shared preparation rejects reused notes"
    (!(WithdrawalSession.requestsMany #[firstShared, firstShared] 1).isOk)
  let changed := { secondShared with capturedBlockHash := word 9 }
  require "shared preparation rejects different captured histories"
    (!(WithdrawalSession.requestsMany #[firstShared, changed] 1).isOk)
  WithdrawalSession.revalidateWith (← mock selected {}) session
  WithdrawalSession.revalidateWith (← mock selected { advancedPool := true }) session
  expectFailure "session rejects evicted root"
    (WithdrawalSession.revalidateWith (← mock selected { knownRoot := false }) session)
  expectFailure "session rejects spent note at fresh block"
    (WithdrawalSession.revalidateWith (← mock selected { spentMismatch := true }) session)
  expectFailure "session rejects changed chain"
    (WithdrawalSession.revalidateWith (← mock selected { wrongChain := true }) session)
  expectFailure "session rejects changed block identity"
    (WithdrawalSession.revalidateWith (← mock selected { changedBlockHash := true }) session)
  let output ← History.inspect good selected
  require "history output" (output ==
    s!"Pool: 0.01 ETH ({poolAddress})\nDeposit: {transactionHash} at block {poolBlock}\nSpent: no at checked block {poolBlock}\n")
  require "no note secret in output" (!output.contains selected.note.preimage)
  let reportText ← History.inspectJson good selected
  let report ← checked "unspent report JSON" (Json.parse reportText)
  let unspentNullifier ← checked "unspent nullifier" (report.getObjVal? "nullifierHash")
  let reportDeposit ← checked "report deposit" (report.getObjVal? "deposit")
  require "redacted unspent report" (unspentNullifier == Json.null &&
    (← getString reportDeposit "transactionHash") == transactionHash &&
    !reportText.contains selected.note.preimage)
  let withdrawn ← mock selected { withWithdrawal := true }
  let withdrawnOutput ← History.inspect withdrawn selected
  require "spent history output" (withdrawnOutput ==
    s!"Pool: 0.01 ETH ({poolAddress})\nDeposit: {transactionHash} at block {poolBlock}\nSpent: yes at checked block {poolBlock}\nWithdrawal: {transactionHash} at block {poolBlock}\nRecipient: 0x00000000000000000000000000000000000000cc\n")
  let spentText ← History.inspectJson withdrawn selected
  let spentReport ← checked "spent report JSON" (Json.parse spentText)
  let spentNullifier ← checked "spent nullifier" (spentReport.getObjVal? "nullifierHash")
  let spentWithdrawal ← checked "spent withdrawal" (spentReport.getObjVal? "withdrawal")
  require "spent report evidence" (spentNullifier == toJson selected.publicIdentity.nullifierHash &&
    (← getString spentWithdrawal "recipient") ==
      "0x00000000000000000000000000000000000000cc" &&
    (← getString spentWithdrawal "feeBaseUnits") == "3" &&
    !spentText.contains selected.note.preimage)
  let missing ← mock selected { omitLog := true }
  expectFailure "omitted deposit does not produce history" (History.inspect missing selected)
  let spent ← mock selected { spentMismatch := true }
  expectFailure "omitted withdrawal conflicts with spent" (History.inspect spent selected)
  let reverted ← mock selected { revertedReceipt := true }
  expectFailure "reverted receipt does not verify" (History.inspect reverted selected)
  let reorg ← mock selected { changedBlockHash := true }
  expectFailure "head hash changes during evidence" (History.inspect reorg selected)
  let wrongChain ← mock selected { wrongChain := true }
  expectFailure "wrong RPC chain" (History.inspect wrongChain selected)
  let echoed ← mock selected { echoNullifierError := true }
  let masked ← try
      let _ ← History.inspect echoed selected
      pure false
    catch error => pure (!error.toString.contains selected.publicIdentity.nullifierHash)
  require "RPC cannot echo selected nullifier in error output" masked
  let help ← History.historyCommand ["--help"]
  require "runnable history help" (help.startsWith "Usage: tornado history")
  let reportHelp ← History.complianceReportCommand ["--help"]
  require "runnable report help" (reportHelp.startsWith "Usage: tornado compliance report")
  expectFailure "missing protected backup path" (History.historyCommand [])
  expectFailure "missing protected report path" (History.complianceReportCommand ["--note-file", "backup"])
  IO.println "PASS: native history and redacted compliance report, exact-block receipt evidence, privacy filter, and fault gates"

end Tornado.Cli.History.Test

def main : IO Unit := Tornado.Cli.History.Test.main
