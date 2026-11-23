import Tornado.Cli.BatchWithdrawalStatus

namespace Tornado.Cli.BatchWithdrawalStatus.Test

open Lean Tornado.Runtime
open Tornado.Cli.BatchWithdrawalStatus

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (json : Json) (name : String) : IO Json :=
  unwrap (json.getObjVal? name)

private def string (json : Json) (name : String) : IO String := do
  unwrap (← field json name).getStr?

private def put (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj entries => .obj (entries.insert name value)
  | other => other

private def withoutField (json : Json) (name : String) : Json :=
  match json with
  | .obj entries => .obj (entries.erase name)
  | other => other

private def wordAddress (raw : String) : String :=
  String.ofList (List.replicate 24 '0') ++ String.ofList (raw.toList.drop 2)

private def zeroWord : String := String.ofList (List.replicate 64 '0')

private def statusName (character : Char) : String :=
  "/tmp/tornado-withdraw-1-" ++
    String.ofList (List.replicate 64 character) ++ ".json"

private def event (pool nullifier recipient relayer fee : String) : Json :=
  Json.mkObj [
    ("poolAddress", toJson pool), ("nullifierHash", toJson nullifier),
    ("recipient", toJson recipient), ("relayer", toJson relayer),
    ("fee", toJson fee)]

private def requireStatus (record : Json)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json)
    (expected : CandidateStatus) : IO Observation := do
  let result ← reconcileWith record.compress fetchChain fetchBundler
  require (result.status == expected) s!"Expected {expected.text} batch status."
  return result

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  require failed message

private def memoryStore (initial : Array (String × Json))
    (failureAt : Option Nat := none) (writeBeforeFailure : Bool := false) :
    IO (Store × IO.Ref (Array (String × ByteArray)) × IO.Ref Nat) := do
  let files ← IO.mkRef (initial.map (fun (path, json) => (path, json.compress.toUTF8)))
  let writes ← IO.mkRef (0 : Nat)
  let read (path : String) : IO ByteArray := do
    let some item := (← files.get).find? (fun item => item.1 == path)
      | throw <| IO.userError "Missing test mirror"
    return item.2
  let replace (path : String) (expected next : ByteArray) : IO Unit := do
    let count ← writes.get
    writes.set (count + 1)
    let values ← files.get
    let some index := values.findIdx? (fun item => item.1 == path)
      | throw <| IO.userError "Missing test mirror"
    if values[index]!.2 != expected then throw <| IO.userError "Injected stale CAS"
    if failureAt == some count then
      if writeBeforeFailure then files.set (values.set! index (path, next))
      throw <| IO.userError "Injected write outcome unknown"
    files.set (values.set! index (path, next))
  return (⟨read, replace⟩, files, writes)

private def storedJson (files : IO.Ref (Array (String × ByteArray))) (index : Nat) : IO Json := do
  let values ← files.get
  let some text := String.fromUTF8? values[index]!.2 | throw <| IO.userError "Invalid stored UTF8"
  unwrap (Json.parse text)

private def persistenceChecks (record candidate fullReceipt : Json) (confirmed : Observation)
    (fetch : Json → JsonRpc.Method → Array Json → IO Json)
    (noBundler : JsonRpc.Method → Array Json → IO Json) : IO Unit := do
  let mirrorWithoutHint := put record "candidates"
    (toJson #[withoutField candidate "transactionHash"])
  let (store, stored, writes) ← memoryStore #[(statusName 'a', mirrorWithoutHint), (statusName 'b', record)]
  let saved ← reconcileAndPersistWith (statusName 'a') store (fetch fullReceipt) noBundler
  require (saved.complete && saved.acknowledgedMirrors == 2 && saved.totalMirrors == 2 &&
    (← writes.get) == 3 && saved.observation.status == .confirmed)
    "All-mirror update or authoritative completion commit failed."
  let firstStored ← storedJson stored 0
  let secondStored ← storedJson stored 1
  let firstParsed ← unwrap (parseRecord firstStored)
  let secondParsed ← unwrap (parseRecord secondStored)
  require (firstParsed.candidates.size == 1 && secondParsed.candidates.size == 1 &&
    firstParsed.candidates[0]!.transactionHash == confirmed.transactionHash &&
    secondParsed.candidates[0]!.transactionHash == confirmed.transactionHash &&
    (← string (← field firstStored "nativeBatchStatusSync") "state") == "complete" &&
    (← string (← field secondStored "nativeBatchStatusSync") "state") == "in-progress")
    "Candidate hints or authoritative completion marker were lost."
  let (partialStore, partialFiles, partialWrites) ← memoryStore
    #[(statusName 'a', record), (statusName 'b', record)] (some 1) true
  let partialResult ← reconcileAndPersistWith (statusName 'a') partialStore (fetch fullReceipt) noBundler
  require (!partialResult.complete && partialResult.acknowledgedMirrors == 1 &&
    (← partialWrites.get) == 2 && !partialResult.message.isEmpty)
    "An ambiguous partial mirror write was reported complete."
  let partialFirst ← storedJson partialFiles 0
  require ((← string (← field partialFirst "nativeBatchStatusSync") "state") == "in-progress")
    "Partial update erased its durable in-progress marker."
  let partialRows ← (← partialFiles.get).mapM fun (path, bytes) => do
    let some raw := String.fromUTF8? bytes | throw <| IO.userError "Bad partial test bytes"
    return (path, ← unwrap (Json.parse raw))
  let (resumeStore, resumedFiles, _) ← memoryStore partialRows
  let resumed ← reconcileAndPersistWith (statusName 'b') resumeStore (fetch fullReceipt) noBundler
  require (resumed.complete &&
    (← unwrap <| parseRecord (← storedJson resumedFiles 0)).candidates.size == 1)
    "Partial update could not be recovered from either mirror."
  let (commitStore, commitFiles, _) ← memoryStore
    #[(statusName 'a', record), (statusName 'b', record)] (some 2)
  let commitFailed ← reconcileAndPersistWith (statusName 'a') commitStore (fetch fullReceipt) noBundler
  require (!commitFailed.complete && commitFailed.acknowledgedMirrors == 2 &&
    (← string (← field (← storedJson commitFiles 0) "nativeBatchStatusSync") "state") == "in-progress")
    "Failed authoritative finalization was reported complete."
  let (missingStore, _, missingWrites) ← memoryStore #[(statusName 'a', record)]
  rejects (reconcileAndPersistWith (statusName 'a') missingStore (fetch fullReceipt) noBundler)
    "A missing mirror was accepted before rewriting other files."
  require ((← missingWrites.get) == 0) "Missing mirror detection changed another reservation."
  let changedHash := "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
  let extraCandidate := put (withoutField candidate "transactionHash") "userOpHash" (toJson changedHash)
  let changedMirror := put record "candidates" (toJson #[candidate, extraCandidate])
  let (mismatchedStore, _, mismatchWrites) ← memoryStore
    #[(statusName 'a', record), (statusName 'b', changedMirror)]
  rejects (reconcileAndPersistWith (statusName 'a') mismatchedStore (fetch fullReceipt) noBundler)
    "Different mirror candidate sets were accepted."
  require ((← mismatchWrites.get) == 0) "Candidate mismatch altered a reservation."
  let (racingStore, racingFiles, _) ← memoryStore
    #[(statusName 'a', record), (statusName 'b', record)]
  let raced ← IO.mkRef false
  let racingFetch : JsonRpc.Method → Array Json → IO Json := fun method params => do
    if !(← raced.get) then
      raced.set true
      let values ← racingFiles.get
      racingFiles.set (values.set! 1 (statusName 'b', changedMirror.compress.toUTF8))
    fetch fullReceipt method params
  let raceResult ← reconcileAndPersistWith (statusName 'a') racingStore racingFetch noBundler
  require (!raceResult.complete && raceResult.acknowledgedMirrors == 1 &&
    (← unwrap <| parseRecord (← storedJson racingFiles 1)).candidates.size == 2)
    "A raced new signed candidate was overwritten or reported synchronized."
  let conflictingMirror := put record "candidates" (toJson #[put candidate "transactionHash" (toJson changedHash)])
  let (conflictStore, _, conflictWrites) ← memoryStore
    #[(statusName 'a', record), (statusName 'b', conflictingMirror)]
  rejects (reconcileAndPersistWith (statusName 'a') conflictStore (fetch fullReceipt) noBundler)
    "Conflicting candidate transaction hashes were overwritten."
  require ((← conflictWrites.get) == 0) "Conflicting hints changed a reservation."
  let payload := Json.mkObj [("publicSignedPayload", toJson ("unchanged" : String))]
  let payloadHash := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  let native := put (put (put record "signedOperation" payload)
    "signedPayloadHash" (toJson payloadHash)) "releaseReservations" (toJson false)
  for (older, newer) in #[("reserved", "exposed"), ("exposed", "submitted"),
      ("submitted", "unknown")] do
    let first := put native "phase" (toJson older)
    let second := put native "phase" (toJson newer)
    let (phaseStore, phaseFiles, _) ← memoryStore
      #[(statusName 'a', first), (statusName 'b', second)]
    let repaired ← reconcileAndPersistWith (statusName 'a') phaseStore (fetch fullReceipt) noBundler
    require (repaired.complete && repaired.observation.status == .confirmed)
      "Interrupted exposure-phase mirrors could not reconcile their exact receipt."
    for i in [0:2] do
      let value ← storedJson phaseFiles i
      require ((← string value "phase") == newer &&
        (← field value "signedOperation") == payload &&
        (← string value "signedPayloadHash") == payloadHash &&
        (← field value "releaseReservations") == toJson false)
        "Phase repair downgraded exposure or changed signed payload/reservation identity."
  let first := put native "phase" (toJson ("reserved" : String))
  let altered := put (put native "phase" (toJson ("unknown" : String)))
    "signedOperation" (Json.mkObj [("publicSignedPayload", toJson ("CHANGED" : String))])
  let (alteredStore, _, alteredWrites) ← memoryStore
    #[(statusName 'a', first), (statusName 'b', altered)]
  rejects (reconcileAndPersistWith (statusName 'a') alteredStore (fetch fullReceipt) noBundler)
    "Phase repair accepted a changed signed payload."
  require ((← alteredWrites.get) == 0) "Changed payload altered another mirror."
  let (badPhaseStore, _, badPhaseWrites) ← memoryStore
    #[(statusName 'a', first),
      (statusName 'b', put native "phase" (toJson ("safe-to-retry" : String)))]
  rejects (reconcileAndPersistWith (statusName 'a') badPhaseStore (fetch fullReceipt) noBundler)
    "Unknown native exposure phase was accepted."
  require ((← badPhaseWrites.get) == 0) "Invalid phase changed another mirror."

def main : IO UInt32 := do
  try
    let vectors ← unwrap (Json.parse (← IO.FS.readFile "fixtures/rpc-receipt-vectors.json"))
    let expected ← field vectors "expected"
    let responses ← field vectors "responses"
    let entryPoint := Tornado.Cli.SmartAccountShow.entryPoint
    let paymaster := "0xB0FfCdC890E969579D348F519a9C3920C2DD04a5"
    let pool := "0x12D66f87A04A9E220743712cE6d9bB1B5616B8Fc"
    let txHash ← string expected "transactionHash"
    let userOpHash ← string expected "userOpHash"
    let sender ← string expected "sender"
    let recipient ← string expected "recipient"
    let relayer ← string expected "relayer"
    let nullifierOne ← string expected "nullifierHash"
    let nullifierTwo := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    let receipt ← field (← field responses "chain") "result"
    let logs ← unwrap (← field receipt "logs").getArr?
    let entryLog := logs[0]!
    let entryTopics ← unwrap (← field entryLog "topics").getArr?
    let entryLog := put (put entryLog "address" (toJson entryPoint)) "topics"
      (toJson (entryTopics.set! 3 (toJson ("0x" ++ wordAddress paymaster))))
    let firstLog := put logs[1]! "address" (toJson pool)
    let firstTopics ← unwrap (← field firstLog "topics").getArr?
    let secondTopics := firstTopics.set! 1 (toJson ("0x" ++ zeroWord))
    let secondData := "0x" ++ wordAddress sender ++
      String.ofList (nullifierTwo.toList.drop 2) ++ zeroWord
    let secondLog := put (put (put firstLog "topics" (toJson secondTopics))
      "data" (toJson secondData)) "logIndex" (toJson ("0x2" : String))
    let fullReceipt := put (put receipt "to" (toJson entryPoint))
      "logs" (toJson #[entryLog, firstLog, secondLog])
    let events := #[
      event pool nullifierOne recipient relayer "0x3e8",
      event pool nullifierTwo sender "0x0000000000000000000000000000000000000000" "0x0"]
    let candidate := Json.mkObj [
      ("userOpHash", toJson userOpHash), ("events", toJson events),
      ("status", toJson ("unknown" : String)), ("transactionHash", toJson txHash)]
    let record := Json.mkObj [
      ("version", toJson (1 : Nat)), ("kind", toJson ("batch-4337" : String)),
      ("chainId", toJson (1 : Nat)),
      ("rpcUrl", toJson ("https://ethereum.publicnode.com" : String)),
      ("bundlerUrl", toJson ("https://bundler.example" : String)),
      ("userOpHash", toJson userOpHash), ("entryPointAddress", toJson entryPoint),
      ("sender", toJson sender), ("paymaster", toJson paymaster),
      ("nonce", toJson ("0x2a" : String)),
      ("fromBlock", toJson ("0x1234" : String)),
      ("events", toJson events), ("candidates", toJson #[candidate]),
      ("statusFiles", toJson #[statusName 'a', statusName 'b']),
      ("status", toJson ("unknown" : String))]
    require ((parseRecord record).isOk) "Valid pinned batch record was rejected."
    let fetch (served : Json) : JsonRpc.Method → Array Json → IO Json := fun method params =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .getTransactionReceipt => do
          require (params == #[toJson txHash]) "Queried another transaction."
          pure served
      | _ => throw <| IO.userError "Unexpected chain RPC method."
    let noBundler : JsonRpc.Method → Array Json → IO Json := fun _ _ =>
      throw <| IO.userError "Recorded transaction hash should skip the bundler."
    let confirmed ← requireStatus record (fetch fullReceipt) noBundler .confirmed
    require (confirmed.transactionHash.isSome && confirmed.candidates.size == 1 &&
      confirmed.candidates[0]!.status == .confirmed)
      "All-events confirmation omitted exact candidate evidence."
    persistenceChecks record candidate fullReceipt confirmed fetch noBundler
    let missingPool := put fullReceipt "logs" (toJson #[entryLog, firstLog])
    let _ ← requireStatus record (fetch missingPool) noBundler .unknown
    let wrongRecipient := put record "events" (toJson #[
      event pool nullifierOne sender relayer "0x3e8", events[1]!])
    let wrongCandidate := put candidate "events" (← field wrongRecipient "events")
    let wrongRecipient := put wrongRecipient "candidates" (toJson #[wrongCandidate])
    let _ ← requireStatus wrongRecipient (fetch fullReceipt) noBundler .unknown
    let wrongPaymaster := put entryLog "topics" (toJson entryTopics)
    let wrongPaymasterReceipt := put fullReceipt "logs"
      (toJson #[wrongPaymaster, firstLog, secondLog])
    let _ ← requireStatus record (fetch wrongPaymasterReceipt) noBundler .unknown
    let noReceipt : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getTransactionReceipt then pure .null else fetch fullReceipt method params
    let _ ← requireStatus record noReceipt noBundler .unknown
    let entryData ← string entryLog "data"
    let failedData := String.ofList
      (entryData.toList.take 66 ++ zeroWord.toList ++ entryData.toList.drop 130)
    let failedEntry := put entryLog "data" (toJson failedData)
    let failedReceipt := put fullReceipt "logs" (toJson #[failedEntry])
    let failed ← requireStatus record (fetch failedReceipt) noBundler .failed
    require ((failed.message.toLower.splitOn "sponsoring note").length > 1)
      "Failed batch omitted the sponsoring-note recovery warning."
    let secondHash := "0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
    let secondCandidate := put (withoutField candidate "transactionHash")
      "userOpHash" (toJson secondHash)
    let twoCandidates := put record "candidates" (toJson #[candidate, secondCandidate])
    let unknownBundler : JsonRpc.Method → Array Json → IO Json := fun _ _ => pure .null
    let unknownScan : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then pure (toJson (#[] : Array Json))
      else fetch fullReceipt method params
    let mixed ← requireStatus twoCandidates unknownScan unknownBundler .confirmed
    require (mixed.candidates.size == 2 &&
      mixed.candidates[0]!.status == .confirmed &&
      mixed.candidates[1]!.status == .unknown)
      "Unresolved second signature was not retained."
    let failedUnknownScan : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then pure (toJson (#[] : Array Json))
      else fetch failedReceipt method params
    let failedUnknown ← requireStatus twoCandidates failedUnknownScan unknownBundler .unknown
    require (failedUnknown.candidates[0]!.status == .failed &&
      failedUnknown.candidates[1]!.status == .unknown)
      "A failed signed candidate masked an unresolved candidate."
    let unsigned := withoutField candidate "transactionHash"
    let fromBundler := put record "candidates" (toJson #[unsigned])
    let bundled : JsonRpc.Method → Array Json → IO Json := fun method params => do
      require (method == .getUserOperationReceipt && params == #[toJson userOpHash])
        "Bundler lookup used the wrong UserOperation."
      pure (Json.mkObj [
        ("userOpHash", toJson userOpHash),
        ("receipt", Json.mkObj [("transactionHash", toJson txHash)])])
    let _ ← requireStatus fromBundler (fetch fullReceipt) bundled .confirmed
    let logFetch (matching : Array Json) : JsonRpc.Method → Array Json → IO Json :=
      fun method params =>
        if method == .getLogs then do
          require (params.size == 1) "EntryPoint log scan has wrong arity."
          let filter := params[0]!
          require ((← string filter "address") == entryPoint.toLower &&
            (← string filter "fromBlock") == "0x1234" &&
            (← string filter "toBlock") == "latest")
            "EntryPoint log scan has wrong filter or range."
          let topics ← unwrap (← field filter "topics").getArr?
          require (topics.size == 2 && topics[1]! == toJson userOpHash)
            "EntryPoint log scan lost the selected UserOperation hash."
          pure (toJson matching)
        else fetch fullReceipt method params
    let nullBundler : JsonRpc.Method → Array Json → IO Json := fun _ _ => pure .null
    let _ ← requireStatus fromBundler (logFetch #[entryLog]) nullBundler .confirmed
    let _ ← requireStatus fromBundler (logFetch #[entryLog, entryLog])
      nullBundler .unknown
    let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .chainId then pure (toJson ("0xaa" : String))
      else fetch fullReceipt method params
    let wrongChainAccepted ← try
      let _ ← reconcileWith record.compress wrongChain noBundler
      pure true
    catch _ => pure false
    require (!wrongChainAccepted) "Wrong-chain RPC was accepted."
    let badCandidate := put candidate "events" (toJson #[events[1]!, events[0]!])
    require (!(parseRecord (put record "candidates" (toJson #[badCandidate]))).isOk)
      "Candidate with changed note order was accepted."
    require (!(parseRecord (put record "statusFiles"
      (toJson #[statusName 'a', "/tmp/../tmp/tornado-withdraw-1-" ++
        String.ofList (List.replicate 64 'b') ++ ".json"]))).isOk)
      "Noncanonical batch status path was accepted."
    IO.println "PASS: batch-4337 exact receipt, all selected events, candidate and path binding, ambiguous scan"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.BatchWithdrawalStatus.Test

def main : IO UInt32 := Tornado.Cli.BatchWithdrawalStatus.Test.main
