import Tornado.Cli.WithdrawalJournal
import Tornado.Cli.WithdrawalNetwork
import Tornado.Cli.WithdrawalSession
import Tornado.Cli.WithdrawalStatusCommand
import Tornado.Cli.WithdrawBatch
import Tornado.Cli.RelayerWithdraw
import Tornado.Runtime.ProofBlinding
import Tornado.Runtime.ProtectedTxSender

/-! Explicitly experimental runnable withdrawals. The parent opens no note
backup: metadata, witnesses, proofs and note-derived signatures are produced
by the separate Lean worker. Its arithmetic is variable-time and does not
guarantee secret erasure. Tests use public fixtures and injected effects. -/

namespace Tornado.Cli.SponsoredWithdraw

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.UserOperation08

private def fail (message : String) : IO α := throw <| IO.userError message
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error message => fail message

structure Options where
  file : Option String := none
  keyFile : Option String := none
  recipient : Option String := none
  callsFile : Option String := none
  noteIndex : Option String := none
  chain : String := "1"
  route : String := "4337"
  rpc : Option String := none
  bundler : Option String := none
  simulationRpc : Option String := none
  assetsDir : Option String := none
  cacheDir : Option String := none
  provingRoot : Option String := none
  statusDir : String := "."
  simulationPolicy : PaymasterPrepare.Policy := .required
  executionGasRetry : Bool := false
  yes : Bool := false
  retryRejected : Bool := false
  experimental : Bool := false
  dryRun : Bool := false
  preflight : Bool := false
  help : Bool := false
  deriving Inhabited

private def valueOption (name value : String) (options : Options) : Except String Options := do
  match name with
  | "--note-file" | "--notes-file" => return { options with file := some value }
  | "--owner-key-file" => return { options with keyFile := some value }
  | "--recipient" | "--receiver" => return { options with recipient := some value }
  | "--contract-calls" => return { options with callsFile := some value }
  | "--note-index" => return { options with noteIndex := some value }
  | "--chain" => return { options with chain := value }
  | "--route" => return { options with route := value }
  | "--rpc" => return { options with rpc := some value }
  | "--bundler-url" => return { options with bundler := some value }
  | "--simulation-rpc" => return { options with simulationRpc := some value }
  | "--assets-dir" => return { options with assetsDir := some value }
  | "--history-cache-dir" => return { options with cacheDir := some value }
  | "--proving-assets-root" => return { options with provingRoot := some value }
  | "--status-dir" => return { options with statusDir := value }
  | "--simulation-policy" =>
    if value == "required" then return { options with simulationPolicy := .required }
    if value == "best-effort" then return { options with simulationPolicy := .bestEffort }
    throw "Use --simulation-policy required or best-effort."
  | _ => throw s!"error: unknown option '{name}'"

def parseOptions : List String → Options → Except String Options
  | [], options => .ok options
  | "--help" :: _, options | "-h" :: _, options => .ok { options with help := true }
  | "--experimental-send" :: rest, options => parseOptions rest { options with experimental := true }
  | "--dry-run" :: rest, options => parseOptions rest { options with dryRun := true }
  | "--preflight" :: rest, options => parseOptions rest { options with preflight := true }
  | "--yes" :: rest, options => parseOptions rest { options with yes := true }
  | "--retry-rejected" :: rest, options => parseOptions rest { options with retryRejected := true }
  | "--execution-gas-retry" :: rest, options => parseOptions rest { options with executionGasRetry := true }
  | name :: rest, options => do
    let pieces := name.splitOn "="
    if pieces.length >= 2 then
      parseOptions rest (← valueOption pieces[0]! (String.intercalate "=" (pieces.drop 1)) options)
    else match rest with
      | [] => throw s!"Withdrawal option '{name}' is missing its value."
      | value :: tail => parseOptions tail (← valueOption name value options)

def absolute (path : String) : IO String := do
  let current ← IO.currentDir
  let source := System.FilePath.mk path
  let value := if source.isAbsolute then source.toString else (current / source).toString
  let mut components : List String := []
  for component in value.splitOn "/" do
    if component.isEmpty || component == "." then continue
    if component == ".." then components := components.dropLast
    else components := components ++ [component]
  return "/" ++ String.intercalate "/" components

private def address (raw : String) : Except String Nat := do
  return (← parseHexBytes (← WithdrawOne.checkedRecipient raw)).data.foldl
    (fun n byte => n * 256 + byte.toNat) 0

private def runtimePaths (options : Options) : IO (String × String) := do
  let app ← IO.appPath
  let some bin := app.parent | fail "Cannot locate the sibling Lean prover worker."
  let worker := (bin / "tornado_prover_worker").toString
  let root ← match options.provingRoot with
    | some value => absolute value
    | none =>
      let some build := bin.parent | fail "Provide --proving-assets-root."
      let some lake := build.parent | fail "Provide --proving-assets-root."
      let some root := lake.parent | fail "Provide --proving-assets-root."
      pure root.toString
  return (worker, root)

private def endpoints (options : Options) (chain : ChainId) : IO (String × String × Bool) := do
  let envRpc ← IO.getEnv "TORNADO_RPC_URL"
  let envBundler ← IO.getEnv "TORNADO_BUNDLER_URL"
  let rpc := (options.rpc.orElse (fun _ => envRpc)).getD (defaultRpc chain)
  let selected := options.bundler.orElse (fun _ => envBundler)
  let bundler := selected.getD s!"https://public.pimlico.io/v2/{chainNumber chain}/rpc"
  if !HttpTransport.validRpcUrl rpc || !HttpTransport.validRpcUrl bundler then
    fail "Use HTTPS or an explicit loopback HTTP endpoint without credentials."
  return (rpc, bundler, selected.isSome)

private def checkDirect (client : WithdrawalNetwork.Client) (sender : Nat) : IO Unit := do
  client.checkChain
  let senderText ← checked <| Bundler.address sender
  for tag in ["latest", "pending"] do
    let value ← client.rpc .getTransactionCount #[toJson senderText, toJson tag]
    if (← checked <| JsonRpc.parseHexQuantity (← checked value.getStr?)) != 0 then
      fail "The note-derived sender has already been used; no new authorization was signed."
  let code ← checked (← client.rpc .getCode #[toJson senderText, toJson ("latest" : String)]).getStr?
  if code != "0x" then fail "The note-derived sender is already deployed or delegated."
  let nonce ← client.rpc .call #[Json.mkObj [
    ("to", toJson (← checked <| Bundler.address Bundler.entryPoint)),
    ("data", toJson (Bundler.dataHex (Abi.selector "getNonce(address,uint192)" ++
      (← checked <| Abi.addressWord sender) ++ (← checked <| Abi.uintWord 0))))],
    toJson ("latest" : String)]
  let bytes ← checked <| parseHexBytes (← checked nonce.getStr?)
  if bytes.size != 32 || !bytes.data.all (· == 0) then
    fail "The note-derived sender has a nonzero EntryPoint nonce."

private def checkSessions (sessions : Array WithdrawalSession.Session)
    (requests : Array Request) (rpc : String) : IO Unit := do
  if requests.size != sessions.size then fail "Withdrawal selection changed."
  for (session, request) in sessions.zip requests do
    if !session.metadata.matchesRequest request ||
        session.history.state.verifiedRoot != some request.root then
      fail "Prepared public inputs differ from the selected note history."
    WithdrawalSession.revalidateLive rpc session

private def expectedEvents (review : WithdrawalSend.Review) : Except String (List Events.ExpectedWithdrawal) :=
  review.notes.toList.mapM fun note => do
    return {
      pool := note.request.pool, recipient := note.request.recipient,
      nullifierHash := ← Abi.uintWord note.request.nullifierHash,
      relayer := note.request.relayer, fee := note.request.fee }

private def approve (text : String) : IO Unit := do
  IO.println "EXPERIMENTAL: the isolated Lean prover uses variable-time arithmetic and cannot guarantee secret erasure."
  IO.println text
  IO.println "Type WITHDRAW to sign and submit exactly this withdrawal:"
  if jsTrim (← (← IO.getStdin).getLine) != "WITHDRAW" then
    fail "Withdrawal cancelled before signing."

private def reconcile (batch : Bool) (path rpc bundler : String) : IO (String × UInt32) :=
  if batch then BatchWithdrawalStatus.statusCommand
    ["--status-file", path, "--rpc", rpc, "--bundler-url", bundler]
  else WithdrawalStatusCommand.statusCommand
    ["--status-file", path, "--rpc", rpc, "--bundler-url", bundler]

private def confirmedDepth (client : WithdrawalNetwork.Client) (rpc path : String) : IO Unit := do
  let bytes ← ProtectedIO.readPrivate path
  let some text := String.fromUTF8? bytes | fail "Invalid protected withdrawal journal."
  let json ← checked <| Json.parse text
  let hash ← checked <| Bundler.parseHash (← checked <| json.getObjVal? "transactionHash")
  let receipt ← checked <| RpcReceipt.parseReceipt
    (← client.rpc .getTransactionReceipt #[toJson (Bundler.dataHex hash)]) hash
  if !receipt.success then fail "Withdrawal transaction has no successful receipt."
  ProtectedTxSender.waitReceiptDepth rpc receipt

/-- Expensive proof generation does not consume the final review window.
The native refresh callback must recheck the exact known roots, account and
current gas-price policy before the clock starts; no fee or proof is changed. -/
def finishPreparationWith (prepare : IO PaymasterPrepare.Prepared)
    (refresh : PaymasterPrepare.Prepared → IO Unit) (now : IO Nat) :
    IO (PaymasterPrepare.Prepared × Nat) := do
  let prepared ← prepare
  refresh prepared
  return (prepared, ← now)

private def runSponsored (options : Options) (batch : Bool) : IO (String × UInt32) := do
  if options.dryRun || options.preflight || !options.experimental then
    fail "Choose --experimental-send separately from --dry-run and --preflight."
  if options.yes then fail "Experimental withdrawals require typed WITHDRAW approval; --yes is unavailable."
  if options.retryRejected then fail "Existing attempts must be reconciled; experimental withdrawals do not replace a reserved candidate."
  if options.route != "4337" then fail "Sponsored withdrawals require --route 4337."
  let some inputFile := options.file | fail "Provide a protected note backup."
  let noteFile ← absolute inputFile
  let chain ← checked <| parseChainInput options.chain
  let chainId := chainNumber chain
  let (rpc, bundler, customBundler) ← endpoints options chain
  let (worker, provingRoot) ← runtimePaths options
  let metadata ← if batch then ProverWorkerClient.inspectBatchPrototype worker noteFile chainId
    else pure #[← ProverWorkerClient.inspectPrototype worker noteFile chainId options.noteIndex]
  let paths ← metadata.mapM (RelayerWithdraw.statusPath options.statusDir)
  for path in paths do
    if ← (System.FilePath.mk path).pathExists then
      fail s!"A selected note already has an attempt at {path}. Reconcile it before preparing another withdrawal."
  let client ← WithdrawalNetwork.native {
    chainId, rpcUrl := rpc, bundlerUrl := bundler, customBundler,
    simulationRpcUrl := options.simulationRpc, simulationPolicy := options.simulationPolicy }
  client.checkChain
  let mut selectedOwner := 0
  let mut selectedKeyPath := ""
  let mut selectedAccount : Option SmartAccountShow.Account := none
  let mut selectedCalls : Array Abi.ContractCall := #[]
  let recipient ← if batch then do
      let some key := options.keyFile | fail "Provide --owner-key-file for the recoverable smart account."
      selectedKeyPath ← absolute key
      selectedOwner ← NativeSigner.addressFromProtectedFile selectedKeyPath
      let account ← WithdrawBatch.loadAccountWith chain selectedOwner client.rpc
      selectedAccount := some account
      if let some file := options.callsFile then
        let bytes ← ProtectedIO.readPrivate (← absolute file)
        let some text := String.fromUTF8? bytes | fail "Contract call file is not UTF-8."
        selectedCalls ← checked <| WithdrawBatch.parseContractCalls text chain
      let receiver ← options.recipient.mapM (fun raw => checked <| address raw)
      let scope ← checked <| WithdrawBatch.makeScope account receiver selectedCalls
      if metadata.size < (if selectedCalls.isEmpty then 2 else 1) then
        fail "Use multiple notes or at least one post-withdrawal contract call."
      pure scope.recipient
    else do
      if options.keyFile.isSome || options.callsFile.isSome then
        fail "Owner keys and post-withdrawal calls require withdraw batch."
      let some raw := options.recipient | fail "Provide --recipient for a direct withdrawal."
      let identity ← ProverWorkerClient.inspectSignerPrototype worker noteFile metadata[0]! options.noteIndex
      selectedOwner := identity.sender
      checkDirect client selectedOwner
      checked <| address raw
  let owner := selectedOwner
  let keyPath := selectedKeyPath
  let batchAccount := selectedAccount
  let calls := selectedCalls
  let mode : PaymasterPrepare.Mode := match batchAccount with
    | none => .single owner recipient
    | some account => .batch {
        address := account.address, owner := account.owner,
        nonce := account.nonce, deployed := account.deployed } recipient calls
  let sessions ← WithdrawalSession.inspectManyLive rpc metadata options.assetsDir options.cacheDir
  let initialRecipient := batchAccount.map (·.address) |>.getD recipient
  let requests ← checked <| WithdrawalSession.requestsMany sessions initialRecipient
  let some first := sessions[0]? | fail "Select at least one note."
  let block := sessions.foldl (fun n session => min n session.history.capturedHead)
    first.history.capturedHead
  let effects := client.preparationEffects
    (do return (← ProofBlinding.sampleScalarWith Entropy.readKernelRandom).value)
    (fun request => do
      let some index := metadata.findIdx? (fun note => note.matchesRequest request)
        | fail "Prover request is outside the selected note set."
      let noteIndex := if batch then some (toString (index + 1)) else options.noteIndex
      let result ← ProverWorkerClient.runPrototype worker provingRoot noteFile noteIndex request
      return { requestHash := result.responseHash, proof := result.proofBytes, signals := result.signals })
    (fun selected => checkSessions sessions selected rpc)
  let (prepared, preparedAtMs) ← finishPreparationWith
    (PaymasterPrepare.prepareWith effects {
      notes := requests, mode, checkedBlock := block,
      policy := options.simulationPolicy, executionGasRetry := options.executionGasRetry })
    (fun prepared => do
      checkSessions sessions (prepared.notes.map (·.request)) rpc
      client.revalidateGasPrice prepared.quote.gas
      match batchAccount with
      | none => checkDirect client owner
      | some old =>
        if (← WithdrawBatch.loadAccountWith chain owner client.rpc) != old then
          fail "Smart-account identity or nonce changed while proofs were generated.")
    IO.monoMsNow
  let review : WithdrawalSend.Review := {
    mode := match mode with
      | .single sender recipient => .single sender recipient
      | .batch account receiver calls => .batch account receiver calls
    notes := prepared.notes, owner, gas := prepared.quote.gas, preparedAtMs, fromBlock := block }
  let journal ← WithdrawalJournal.create paths
  let signingStarted ← IO.mkRef false
  let senderLock ← if batch then do
      let some parent := (System.FilePath.mk keyPath).parent | fail "Invalid owner key directory."
      let path := (parent / s!".tornado-sender-{chainId}-{(← checked <| Bundler.address owner).toLower}.lock").toString
      let bytes := (Json.mkObj [("version", toJson (1 : Nat)),
        ("kind", toJson ("sender-lock" : String)), ("statusFile", toJson paths[0]!),
        ("purpose", toJson ("smart-account-withdrawal" : String))]).compress.toUTF8
      ProtectedIO.createPrivate path bytes
      pure (some (path, bytes))
    else pure none
  try
    let sendEffects : WithdrawalSend.Effects := {
      rpc := client.send
      approve := approve
      revalidate := fun reviewed => do
        checkSessions sessions (reviewed.notes.map (·.request)) rpc
        client.checkChain
        client.revalidateGasPrice reviewed.gas
        match batchAccount with
        | none => checkDirect client owner
        | some old =>
          if (← NativeSigner.addressFromProtectedFile keyPath) != owner ||
              (← WithdrawBatch.loadAccountWith chain owner client.rpc) != old then
            fail "Smart-account identity, owner or nonce changed after review."
      signDigest := fun hash => do
        signingStarted.set true
        if batch then
          let (signer, signature) ← NativeSigner.signDigest65FromProtectedFile keyPath hash
          return { owner := signer, signature }
        else
          let request : ProverSignerWire.SignRequest := {
            metadata := metadata[0]!, expectedSender := owner, operationHash := hash }
          let signed ← ProverWorkerClient.signPrototype worker noteFile options.noteIndex request
          return {
            owner := signed.identity.sender, signature := signed.operationSignature,
            authorization := some (← checked <| ProverWorkerClient.authorizationOf request signed) }
      reserve := fun reviewed op hash bytes => WithdrawalJournal.reserve journal reviewed op hash bytes rpc bundler
      markExposed := fun hash => WithdrawalJournal.mark journal hash "exposed"
      markSubmitted := fun hash => WithdrawalJournal.mark journal hash "submitted"
      markUnknown := fun hash => WithdrawalJournal.mark journal hash "unknown"
      simulate := fun op => do
        client.simulate op (← checked <| expectedEvents review) prepared.quote.estimation
      nowMs := IO.monoMsNow }
    let outcome ← WithdrawalSend.executeWith sendEffects review
    let hash := match outcome with | .submitted hash | .unknown hash => hash
    let mut last := s!"Withdrawal outcome unknown. Operation: {Bundler.dataHex hash}\n"
    for _ in [0:90] do
      let (output, code) ← try reconcile batch paths[0]! rpc bundler
        catch _ => pure ("No verified receipt yet; do not resend.\n", 2)
      last := output
      if code == 0 then
        confirmedDepth client rpc paths[0]!
        if let some (path, bytes) := senderLock then ProtectedIO.removePrivateExact path bytes
        return (output ++ s!"Twelve confirmations observed. Status file: {paths[0]!}\n", 0)
      IO.sleep 2000
    return (last ++ s!"Status file: {paths[0]!}\nNo replacement was sent; reconcile this candidate before taking further action.\n" ++
      (senderLock.map (fun (path, _) => s!"Sender lock retained: {path}\n")).getD "", 2)
  catch error =>
    if !(← signingStarted.get) then
      if let some (path, bytes) := senderLock then
        try ProtectedIO.removePrivateExact path bytes catch _ => pure ()
    throw error

private def help (batch : Bool) : String :=
  (if batch then "Usage: tornado withdraw batch --notes-file <path> --owner-key-file <path> [options]\n"
    else "Usage: tornado withdraw one --note-file <path> --recipient <address> [options]\n") ++
  "Use --dry-run for review, or --experimental-send for the explicitly experimental live path.\n" ++
  "One-note --preflight checks history without signing. --route 4337|relayer selects the one-note route.\n" ++
  "Live withdrawals require typed WITHDRAW approval; --yes and replacement retries are unavailable.\n" ++
  "Options: --chain, --rpc, --bundler-url, --status-dir, --assets-dir, --history-cache-dir, --proving-assets-root.\n" ++
  "Batch options: --receiver, --contract-calls, --simulation-rpc, --simulation-policy required|best-effort, --execution-gas-retry.\n" ++
  "The default required policy blocks unavailable simulation. Best-effort only permits narrowly identified unavailability after successful dummy estimation.\n"

def command (batch : Bool) (args : List String) : IO (String × UInt32) := do
  if args.contains "--help" || args.contains "-h" then return (help batch, 0)
  if !args.contains "--experimental-send" then
    if !args.contains "--dry-run" && (batch || !args.contains "--preflight") then
      fail (if batch then "Choose --dry-run or --experimental-send."
        else "Choose --dry-run, --preflight or --experimental-send.")
    return (← if batch then WithdrawBatch.withdrawBatchCommand args
      else WithdrawOne.withdrawOneCommand args, 0)
  let options ← checked <| parseOptions args {}
  if batch && (options.route != "4337" || options.noteIndex.isSome) then
    fail "Batch withdrawals require the complete selected backup and the 4337 route."
  if !batch && options.route == "relayer" then
    if options.keyFile.isSome || options.callsFile.isSome || options.simulationRpc.isSome ||
        options.executionGasRetry then
      fail "Owner keys, contract calls and execution simulation options require the batch 4337 route."
    let some noteFile := options.file | fail "Provide --note-file."
    let some recipient := options.recipient | fail "Provide --recipient."
    if options.dryRun || options.preflight then fail "Choose only one withdrawal mode."
    let chain ← checked <| parseChainInput options.chain
    let (rpc, _, _) ← endpoints options chain
    let (worker, root) ← runtimePaths options
    return ← RelayerWithdraw.run {
      noteFile, recipient, workerPath := worker, provingRoot := root, rpcUrl := rpc,
      chainId := chainNumber chain, noteIndex := options.noteIndex, assetsDir := options.assetsDir,
      cacheDir := options.cacheDir, statusDir := options.statusDir,
      experimental := true, retryRejected := options.retryRejected, yes := options.yes }
  runSponsored options batch

end Tornado.Cli.SponsoredWithdraw
