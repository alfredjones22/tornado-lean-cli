import Tornado.Cli.RelayerWithdraw
import Tornado.Crypto.TornadoSignature

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Cli.RelayerSend

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message
private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message
private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  require failed message
private def field (json : Json) (name : String) : IO Json := checked <| json.getObjVal? name
private def text (json : Json) (name : String) : IO String := do
  checked (← field json name).getStr?
private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes
private def hex (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes
private def quantity (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)
private def address (value : Nat) : String := hex ((word value).extract 12 32)

private def quoteEffects (fixture : Json) : IO Effects := do
  let cfg ← checked <| config 1
  let log ← field fixture "registryEvent"
  let response ← text fixture "aggregatorResponse"
  let status ← field fixture "status"
  return {
    nowMs := pure 0,
    get := fun url => do
      require (url == "https://relayer.example.org/status") "Unexpected quote status URL"
      return status.compress.toUTF8,
    rpc := fun method params => do
      match method with
      | .chainId => return toJson ("0x1" : String)
      | .blockNumber => return toJson (quantity (cfg.registryDeployment + 4))
      | .gasPrice => return toJson ("0x3b9aca00" : String)
      | .getLogs => return Json.arr #[log]
      | .call =>
        require ((← text params[0]! "data") == (← text fixture "aggregatorCall"))
          "Unexpected quote aggregator call"
        return toJson response
      | _ => throw <| IO.userError "Unexpected quote RPC" }

private def prepareFixture (fixture : Json) : IO Prepared := do
  let some pool := poolFor .mainnet "0.1" "ETH" | throw <| IO.userError "Missing original fixture pool"
  let effects ← quoteEffects fixture
  let quote ← prepareWith effects pool
  let publicNote ← checked <| tornadoSignatureNote
    (word 0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb)
    1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let tree ← checked <| buildMimcTree #[publicNote.commitment]
  let path ← checked <| mimcProofAt tree 0
  -- The circuit itself does not encode a pool address. This is an unfunded
  -- synthetic original-pool history using the same public preimage fixture.
  let request : Request := {
    chainId := 1, pool := 0x12d66f87a04a9e220743712ce6d9bb1b5616b8fc,
    commitment := publicNote.commitment, nullifierHash := publicNote.nullifierHash,
    leafIndex := 0, root := tree.root, siblings := path.siblings,
    pathIndices := path.pathIndices, recipient := 1,
    relayer := quote.relayer.rewardAccount, fee := quote.amounts.fee, refund := 0 }
  let proofFixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/groth16-relayer-public-proof.json")
  let proof ← checked <| parseHexBytes (← text proofFixture "solidityProofHex")
  let rawSignals ← checked (← field proofFixture "publicSignals").getArr?
  let signals ← rawSignals.mapM fun value => do
    let raw ← checked value.getStr?
    let some number := raw.toNat? | throw <| IO.userError "Invalid public signal fixture"
    return number
  require (signals == request.publicSignals) "Relayer fixture differs from reviewed public signals"
  let result : Result := ⟨request.hash, proof, signals⟩
  require (!(prepareProof quote { request with recipient := 2 } result).isOk)
    "A proof was rebound to a changed recipient"
  require (!(prepareProof quote { request with relayer := 188 } result).isOk)
    "A proof was rebound to a changed relayer reward"
  require (!(prepareProof quote request { result with proof := proof.set! 0 0xff }).isOk)
    "Malformed proof coordinates were accepted"
  checked <| prepareProof quote request result

structure Faults where
  cancel : Bool := false
  stalePool : Bool := false
  reserveFails : Bool := false
  reserveWrittenThenFails : Bool := false
  lostReply : Bool := false
  badReply : Bool := false
  noChainEvent : Bool := false
  wrongRecipient : Bool := false
  updateFails : Bool := false
  deriving Inhabited

private def executionEffects (fixture : Json) (prepared : Prepared) (faults : Faults) :
    IO (SubmissionEffects × IO.Ref (Array String) × IO.Ref (Option String) × IO.Ref Nat) := do
  let base ← quoteEffects fixture
  let trace ← IO.mkRef (#[] : Array String)
  let journal ← IO.mkRef (none : Option String)
  let posts ← IO.mkRef (0 : Nat)
  let txHash := hex (word 777)
  let blockHash := hex (word 888)
  let block := quantity prepared.quote.fromBlock
  let recipient := if faults.wrongRecipient then 2 else prepared.request.recipient
  let log := Json.mkObj [
    ("address", toJson (address prepared.request.pool)),
    ("blockNumber", toJson block), ("blockHash", toJson blockHash),
    ("transactionHash", toJson txHash), ("transactionIndex", toJson ("0x0" : String)),
    ("logIndex", toJson ("0x0" : String)), ("removed", toJson false),
    ("topics", toJson #[hex Events.withdrawalTopic, hex (word prepared.request.relayer)]),
    ("data", toJson (hex (word recipient ++ word prepared.request.nullifierHash ++ word prepared.request.fee)))]
  let receipt := Json.mkObj [
    ("transactionHash", toJson txHash), ("blockHash", toJson blockHash),
    ("blockNumber", toJson block), ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson (address prepared.request.relayer)),
    ("to", toJson (address prepared.request.pool)), ("status", toJson ("0x1" : String)),
    ("logs", Json.arr #[log])]
  let readonly := { base with rpc := fun method params => do
    if method == .getLogs then
      let target ← text params[0]! "address"
      if target == address prepared.request.pool then
        require ((← posts.get) == 1) "Status scan occurred before the single proof POST"
        return Json.arr (if faults.noChainEvent then #[] else #[log])
    if method == .getTransactionReceipt then
      require (params == #[toJson txHash]) "Queried another relayer transaction"
      return receipt
    base.rpc method params }
  let effects : SubmissionEffects := {
    readonly,
    approve := fun _ => do
      trace.modify (·.push "approve")
      if faults.cancel then throw <| IO.userError "Cancelled",
    revalidate := fun request => do
      trace.modify (·.push "history")
      require (request == prepared.request) "Revalidation used different public inputs"
      if faults.stalePool then throw <| IO.userError "Spent or changed history",
    reserve := fun raw => do
      trace.modify (·.push "reserve")
      if (← journal.get).isSome then throw <| IO.userError "Existing permanent claim"
      if faults.reserveWrittenThenFails then
        journal.set (some raw)
        throw <| IO.userError "Reservation write outcome unknown"
      if faults.reserveFails then throw <| IO.userError "Disk failure"
      journal.set (some raw),
    update := fun raw => do
      trace.modify (·.push "update")
      if faults.updateFails then throw <| IO.userError "CAS failed"
      journal.set (some raw),
    post := fun url body => do
      trace.modify (·.push "post")
      require (url == prepared.quote.relayer.url ++ "v1/tornadoWithdraw" && body == prepared.body)
        "Relayer POST URL or bytes changed"
      let some raw ← journal.get | throw <| IO.userError "Proof exposed before durable claim"
      let record ← checked <| Json.parse raw
      require ((← text record "nativePostBodyHash") == hex (keccak256 body) &&
        (← text record "nativeProofHash") == hex (keccak256 prepared.accepted.proofBytes))
        "Reserved executable payload differs from POST"
      posts.modify (· + 1)
      if faults.lostReply then throw <| IO.userError "Proof POST reply lost"
      if faults.badReply then return "{\"id\":\"bad/id\"}".toUTF8
      return "{\"id\":\"public_job\",\"status\":\"CONFIRMED\"}".toUTF8,
    sleepMs := fun _ => pure () }
  return (effects, trace, journal, posts)

private def submissionTests (fixture : Json) (prepared : Prepared) : IO Unit := do
  let rpc := "https://ethereum.publicnode.com"
  let (effects, trace, _, posts) ← executionEffects fixture prepared {}
  let confirmed ← submitWith effects prepared rpc { waitMs := 0 }
  require (confirmed.code == 0 && confirmed.jobId == some "public_job" &&
    confirmed.journalUpdated && (← posts.get) == 1 &&
    (← trace.get).extract 0 4 == #["approve", "history", "reserve", "post"])
    "Exact relayer submission or reservation ordering failed"
  rejects (submitWith effects prepared rpc { waitMs := 0 }) "Permanent claim allowed a second POST"
  require ((← posts.get) == 1) "A relayer POST was repeated"
  for faults in [({ cancel := true } : Faults), { stalePool := true },
      { reserveFails := true }, { reserveWrittenThenFails := true }] do
    let (effects, _, _, posts) ← executionEffects fixture prepared faults
    rejects (submitWith effects prepared rpc { waitMs := 0 }) "Pre-exposure fault was accepted"
    require ((← posts.get) == 0) "A proof escaped after failed approval/history/reservation"
  let (lost, _, lostJournal, lostPosts) ← executionEffects fixture prepared { lostReply := true, noChainEvent := true }
  let unknown ← submitWith lost prepared rpc { waitMs := 0 }
  require (unknown.code == 2 && unknown.jobId.isNone && (← lostPosts.get) == 1 &&
    (← lostJournal.get).isSome) "Lost POST reply did not preserve the unknown reserved attempt"
  let (recovered, _, _, _) ← executionEffects fixture prepared { lostReply := true }
  let recovered ← submitWith recovered prepared rpc { waitMs := 0 }
  require (recovered.code == 0 && recovered.jobId.isNone)
    "A lost reply could not reconcile from exact pool event and receipt"
  for faults in [({ badReply := true, noChainEvent := true } : Faults),
      { noChainEvent := true }, { wrongRecipient := true }] do
    let (effects, _, _, posts) ← executionEffects fixture prepared faults
    let result ← submitWith effects prepared rpc { waitMs := 0 }
    require (result.code == 2 && (← posts.get) == 1)
      "Malformed/job-only/wrong-recipient evidence confirmed or retried a withdrawal"
  let (failedUpdate, _, _, posts) ← executionEffects fixture prepared { updateFails := true }
  let result ← submitWith failedUpdate prepared rpc { waitMs := 0 }
  require (result.code == 2 && !result.journalUpdated && (← posts.get) == 1)
    "Failed status persistence authorized success or a duplicate POST"

private def slowProverRefreshTests (fixture : Json) (prepared : Prepared) : IO Unit := do
  let base ← quoteEffects fixture
  let slow := { base with nowMs := pure (quoteLifetimeMs + 12345) }
  rejects (recheckWith slow prepared.quote) "An expired original quote survived its review deadline"
  let refreshed ← refreshPreparedWith slow prepared
  require (refreshed.quote.quotedAt == quoteLifetimeMs + 12345 &&
    refreshed.request == prepared.request && refreshed.body == prepared.body &&
    refreshed.accepted.proofBytes == prepared.accepted.proofBytes &&
    refreshed.quote.amounts == prepared.quote.amounts)
    "Post-proof refresh changed executable bytes, public inputs, fees or the review timestamp"
  recheckWith slow refreshed.quote
  let higherGas := { slow with rpc := fun method params => do
    if method == .gasPrice then return toJson ("0x77359400" : String)
    slow.rpc method params }
  rejects (refreshPreparedWith higherGas prepared)
    "Changed proof-bound fee survived the post-proof public refresh"
  let changedEndpoint := { slow with get := fun _ => do
    let status ← field fixture "status"
    return (status.setObjVal! "rewardAccount"
      (toJson ("0x00000000000000000000000000000000000000cc" : String))).compress.toUTF8 }
  rejects (refreshPreparedWith changedEndpoint prepared)
    "Changed relayer reward survived the post-proof public refresh"

private def journalTests (directory : String) (prepared : Prepared) : IO Unit := do
  ProtectedIO.checkPrivateDirectory directory
  let name := "tornado-withdraw-1-" ++ String.ofList (List.replicate 64 'a') ++ ".json"
  let path := directory ++ "/" ++ name
  let journal ← protectedJournal path
  let root ← checked <| statusRecord prepared "https://ethereum.publicnode.com"
  journal.reserve (root.compress ++ "\n")
  let duplicate ← protectedJournal path
  rejects (duplicate.reserve root.compress) "Existing note claim was overwritten"
  let pending := (root.setObjVal! "jobId" (toJson ("public_job" : String))).setObjVal! "status" (toJson ("pending" : String))
  journal.update pending.compress
  let before ← ProtectedIO.readPrivate path
  rejects (journal.update ((pending.setObjVal! "fee" (toJson ("0x1" : String))).compress))
    "The reserved fee was replaced"
  rejects (journal.update ((pending.setObjVal! "jobId" (toJson ("another_job" : String))).compress))
    "The reserved job identifier was replaced"
  require ((← ProtectedIO.readPrivate path) == before) "Rejected update altered the protected claim"
  let raw := (String.fromUTF8? before).getD ""
  require ((raw.splitOn (hex prepared.accepted.proofBytes)).length == 1)
    "The executable proof was stored in the claim"
  let concurrent := (pending.setObjVal! "message" (toJson
    ("A separate status process updated this claim." : String))).compress.toUTF8
  ProtectedIO.replacePrivate path before concurrent
  rejects (journal.update pending.compress) "A stale relayer writer bypassed protected CAS"
  require ((← ProtectedIO.readPrivate path) == concurrent)
    "A CAS conflict erased the other process's protected claim"
  let bad ← protectedJournal (directory ++ "/ordinary-name.json")
  rejects (bad.reserve root.compress) "A nonopaque per-note claim filename was accepted"

def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw <| IO.userError "Usage: relayer_submit_test <private-test-directory>"
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/classic-relayer.json")
  let prepared ← prepareFixture fixture
  slowProverRefreshTests fixture prepared
  submissionTests fixture prepared
  journalTests directory prepared
  rejects (Tornado.Cli.RelayerWithdraw.run {
    noteFile := "/unopened-note", recipient := address 1, workerPath := "/unopened-worker",
    provingRoot := "/unused-assets", rpcUrl := "https://ethereum.publicnode.com" })
    "Experimental relayer mode was enabled implicitly"
  IO.println "PASS: relayer proof binding, reserve-before-POST, single-send ambiguity, exact receipts and protected claims"
  return 0
