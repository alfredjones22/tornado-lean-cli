import Tornado.Cli.ProverWorker
import Tornado.Runtime.ProverWorkerClient
import Tornado.Protocol.SponsoredWithdrawal
import Tornado.Cli.WithdrawalSend
import tests.WithdrawalJournal

/-! End-to-end test using a deterministic, publicly derivable, unfunded note. -/

open Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def fails (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def word (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def keyBytes : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push (if i == 31 then 1 else 0)
  return bytes

def main (args : List String) : IO UInt32 := do
  let [workerPath, assetsRoot, privateDir] := args
    | throw <| IO.userError "Usage: prover_worker_test <worker> <assets-root> <private-test-dir>"
  require ((System.FilePath.mk workerPath).isAbsolute &&
    (System.FilePath.mk assetsRoot).isAbsolute &&
    (System.FilePath.mk privateDir).isAbsolute)
    "Worker test paths must be absolute."
  ProtectedIO.checkPrivateDirectory privateDir
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing public Classic fixture pool."
  let poolNat := word (← checked <| parseHexBytes pool.address)
  let note ← checked <| tornadoSignatureNote keyBytes 1 0 poolNat
  let tree ← checked <| buildMimcTree #[note.commitment]
  let path ← checked <| mimcProofAt tree 0
  let request : Request := {
    chainId := 1, pool := poolNat,
    commitment := note.commitment, nullifierHash := note.nullifierHash,
    leafIndex := path.index, root := path.root,
    siblings := path.siblings, pathIndices := path.pathIndices,
    recipient := 1,
    relayer := ← checked <| SponsoredWithdrawal.paymaster 1,
    fee := 1, refund := 0 }
  let notePath := privateDir ++ "/unfunded-public-note"
  let raw := s!"tornado-eth-0.01-1-0x{bytesToHex note.preimage}"
  ProtectedIO.createPrivate notePath raw.toUTF8
  let requestPath := privateDir ++ "/public-request.json"
  IO.FS.writeFile requestPath (request.encode ++ "\n")
  require (← fails <| Tornado.Cli.ProverWorker.readPublicRequest requestPath)
    "Noncanonical public request was accepted."
  IO.FS.writeFile requestPath request.encode
  let parsed ← Tornado.Cli.ProverWorker.readPublicRequest requestPath
  require (parsed == request) "Public request roundtrip changed values."
  let malformed ← IO.Process.output {
    cmd := workerPath,
    args := #["--assets-root", assetsRoot, "--note-file", notePath,
      "--request-file", requestPath ++ ".missing"] }
  require (malformed.exitCode != 0 && malformed.stdout == "" &&
    malformed.stderr == "Prover worker failed.\n")
    "Worker failure leaked data or used a noncanonical diagnostic."
  require (← fails <| ProverWorkerClient.runPrototype workerPath assetsRoot
    notePath none { request with commitment := request.commitment + 1 })
    "Worker accepted a note/request commitment mismatch."
  let started ← IO.monoMsNow
  let accepted ← ProverWorkerClient.runPrototype workerPath assetsRoot notePath
    none request
  let finished ← IO.monoMsNow
  require (accepted.proofBytes.size == 256 &&
    accepted.signals == request.publicSignals &&
    accepted.calldata.size == 516)
    "Worker proof or calldata differed from the reviewed public request."
  require ((SponsoredWithdrawal.paymaster 1).toOption ==
      some 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5 &&
    (SponsoredWithdrawal.paymaster 11155111).toOption ==
      some 0x835ce2da8ad0d1f5d5a8462a58594006514c39b0)
    "Paymaster networks differ from the installed pinned SDK."
  let publicProof : SponsoredWithdrawal.NoteProof := {
    request := request
    result := {
      requestHash := request.hash
      proof := accepted.proofBytes
      signals := accepted.signals } }
  let gas : SponsoredWithdrawal.Gas := { maxFee := 1000000000, priority := 100000000 }
  let single ← checked <| SponsoredWithdrawal.single publicProof 2 1 gas
  let sponsor ← checked <| Abi.decodeSponsorParameters single.paymasterData
  require (single.callData.isEmpty && single.callGasLimit == 0 && single.factory.isNone &&
    single.sender == 2 && sponsor.recipient == 1 && sponsor.fee == 1 &&
    sponsor.proof == accepted.proofBytes) "Sponsored one-note payout changed"
  let account : SponsoredWithdrawal.Account := {
    address := 1, owner := 2, nonce := 0, deployed := true }
  let calls : Array Abi.ContractCall := #[{ to := 3, value := 0, data := ByteArray.empty }]
  let batch ← checked <| SponsoredWithdrawal.batch #[publicProof] account 1 calls
    { gas with execution := 100000 }
  require (batch.sender == 1 && batch.factory.isNone &&
    batch.callData == (← checked <| Abi.accountExecuteBatch calls))
    "Sponsored account execution changed the ordered user calls"
  -- A different public unfunded note already has an independently generated
  -- SDK proof with recipient=1, relayer=0, fee=0. Reuse it for the execution
  -- note so the test exercises real multi-note ordering without another proof.
  -- These independent synthetic roots test local proof/calldata binding;
  -- they do not attest that one live pool accepts both roots on one chain.
  let directKey ← checked <| parseHexBytes
    "0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb"
  let directNote ← checked <| tornadoSignatureNote directKey 1 0 poolNat
  let directTree ← checked <| buildMimcTree #[directNote.commitment]
  let directPath ← checked <| mimcProofAt directTree 0
  let directRequest : Request := {
    chainId := 1, pool := poolNat,
    commitment := directNote.commitment, nullifierHash := directNote.nullifierHash,
    leafIndex := directPath.index, root := directPath.root,
    siblings := directPath.siblings, pathIndices := directPath.pathIndices,
    recipient := account.address, relayer := 0, fee := 0, refund := 0 }
  let fixture ← checked <| Lean.Json.parse
    (← IO.FS.readFile (assetsRoot ++ "/fixtures/groth16-full-public-proof.json"))
  let proofHex ← checked <| (← checked <| fixture.getObjVal? "solidityProofHex").getStr?
  let directBytes ← checked <| parseHexBytes proofHex
  let directProof : SponsoredWithdrawal.NoteProof := {
    request := directRequest
    result := {
      requestHash := directRequest.hash
      proof := directBytes
      signals := directRequest.publicSignals } }
  let acceptedDirect ← checked <| ProverWorkerClient.acceptResponse
    directProof.request directProof.result
  require (directRequest.nullifierHash != request.nullifierHash &&
    directRequest.commitment != request.commitment)
    "The public multi-note fixture must use distinct notes"
  let directCall : Abi.ContractCall := {
    to := poolNat, value := 0, data := acceptedDirect.calldata }
  let ordered ← checked <| SponsoredWithdrawal.batch #[publicProof, directProof]
    account account.address calls { gas with execution := 600000 }
  require (ordered.callData == (← checked <| Abi.accountExecuteBatch (#[directCall] ++ calls)))
    "Direct withdrawal must precede the exact ordered user actions"
  let forwarded ← checked <| SponsoredWithdrawal.batch #[publicProof, directProof]
    account 4 #[] { gas with execution := 600000 }
  let expectedForward : Abi.ContractCall := {
    to := 4, value := 2 * pool.amount - request.fee, data := ByteArray.empty }
  require (forwarded.callData == (← checked <| Abi.accountExecuteBatch
    #[directCall, expectedForward]))
    "Automatic forwarding changed the recipient or total net payout"
  require (!(SponsoredWithdrawal.batch #[publicProof, directProof] account 1 calls gas).isOk)
    "A batch with executable calls and zero execution gas was accepted"
  require (!(SponsoredWithdrawal.batch #[publicProof, publicProof] account 1 calls
    { gas with execution := 600000 }).isOk)
    "A duplicated selected note was accepted"
  require (!(SponsoredWithdrawal.batch #[directProof, publicProof] account 1 calls
    { gas with execution := 600000 }).isOk)
    "An unsponsored first note was accepted as the gas sponsor"
  let owner := word (← checked <| secp256k1EthereumAddress keyBytes)
  let clock ← IO.monoMsNow
  let review : Tornado.Cli.WithdrawalSend.Review := {
    mode := .batch { account with owner } 1 calls,
    notes := #[publicProof], owner,
    gas := { gas with execution := 100000 },
    preparedAtMs := clock, fromBlock := 1 }
  let events ← IO.mkRef (#[] : Array String)
  let expectedOp ← checked <| Tornado.Cli.WithdrawalSend.build review
  let expectedHash ← checked <| UserOperation08.userOperationHash 1 Bundler.entryPoint expectedOp
  let effects : Tornado.Cli.WithdrawalSend.Effects := {
    rpc := fun _ _ => do
      events.modify (·.push "send")
      return Lean.toJson (Bundler.dataHex expectedHash)
    approve := fun text => do
      require (text.contains '3') "Missing ordered call review"
      events.modify (·.push "approve")
    revalidate := fun _ => events.modify (·.push "revalidate")
    signDigest := fun digest => do
      events.modify (·.push "sign")
      return { owner, signature := (← checked <| secp256k1SignDigest keyBytes digest).bytes65 }
    reserve := fun _ _ hash _ => do
      require (hash == expectedHash) "Changed reserved hash"
      events.modify (·.push "reserve")
    markExposed := fun _ => events.modify (·.push "exposed")
    markSubmitted := fun _ => events.modify (·.push "submitted")
    markUnknown := fun _ => events.modify (·.push "unknown")
    simulate := fun _ => do
      events.modify (·.push "simulate")
      return true
    nowMs := pure clock }
  match ← Tornado.Cli.WithdrawalSend.executeWith effects review with
  | .submitted hash => require (hash == expectedHash) "Wrong submitted hash"
  | .unknown _ => throw <| IO.userError "Valid offline withdrawal failed"
  require ((← events.get) == #["approve", "revalidate", "sign", "reserve",
    "exposed", "simulate", "send", "submitted"])
    "Executable withdrawal escaped before durable reservation"
  events.set #[]
  let rejected := { effects with simulate := fun _ => do
    events.modify (·.push "simulate")
    return false }
  match ← Tornado.Cli.WithdrawalSend.executeWith rejected review with
  | .unknown hash => require (hash == expectedHash) "Simulation lost candidate hash"
  | _ => throw <| IO.userError "Rejected signed simulation was submitted"
  require ((← events.get) == #["approve", "revalidate", "sign", "reserve",
    "exposed", "simulate", "unknown"])
    "Failed simulation permitted a send or lost uncertain state"
  Tornado.Test.WithdrawalJournal.run privateDir publicProof directProof keyBytes gas
  IO.println s!"PASS: isolated public-fixture proof, parent verification, malformed request and sanitized failure ({finished - started} ms)"
  return 0
