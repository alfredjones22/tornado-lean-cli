import Tornado.Protocol.SponsoredWithdrawal

/-! Native, effect-injected alpha.38 paymaster preparation. Gas estimation
uses a fixed dummy proof/signature/authorization and random public nullifier
hashes only. The real proof callback is invoked after bounded estimation has
stabilized. This module handles public protocol data through injected effects. -/

namespace Tornado.Cli.PaymasterPrepare

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.UserOperation08
open Tornado.Protocol.SponsoredWithdrawal

inductive Mode where
  | single (sender recipient : Nat)
  | batch (account : SponsoredWithdrawal.Account) (receiver : Nat)
      (tailCalls : Array Abi.ContractCall)
  deriving Inhabited

inductive Policy where
  | required | bestEffort
  deriving Inhabited, BEq

inductive Unavailable where
  | transport | bundlerInternal
  deriving Inhabited, BEq

inductive EstimateReply where
  | estimated (gas : Json)
  | unavailable (reason : Unavailable)
  | executionOutOfGas
  | rejected
  deriving Inhabited

inductive Estimation where
  | estimated | fallback (reason : Unavailable)
  deriving Inhabited, BEq

structure Input where
  notes : Array Request
  mode : Mode
  checkedBlock : Nat
  policy : Policy := .bestEffort
  tailCallGasEstimate : Option Nat := none
  executionGasRetry : Bool := false
  maxFeeBps : Nat := 10000
  maxBlockLag : Nat := 64
  bounds : Bundler.Bounds := {}
  deriving Inhabited

structure Effects where
  rpc : JsonRpc.Method → Array Json → IO Json
  bundler : JsonRpc.Method → Array Json → IO Json
  /-- Only estimation requests may use this callback. A live adapter must
  classify failures structurally; an arbitrary RPC rejection is not outage. -/
  estimate : Array Json → IO EstimateReply
  randomField : IO Nat
  prove : Request → IO Result
  validateHistory : Array Request → IO Unit

structure Quote where
  input : Input
  gas : Gas
  fee : Nat
  requests : Array Request
  estimation : Estimation
  deriving Inhabited

structure Prepared where
  quote : Quote
  notes : Array NoteProof
  deriving Inhabited

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => throw <| IO.userError "Paymaster preparation rejected invalid public data."

private def fail (message : String) : IO α := throw <| IO.userError message

private def field (json : Json) (name : String) : IO Json :=
  checked <| json.getObjVal? name

private def quantity (json : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked json.getStr?)

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n b => n * 256 + b.toNat) 0

private def data (value : Json) (maximum : Nat) : IO ByteArray := do
  let raw ← checked value.getStr?
  if !raw.startsWith "0x" || raw.length % 2 != 0 ||
      raw.utf8ByteSize > maximum * 2 + 2 then
    fail "Paymaster RPC data exceeds its encoding bound."
  let bytes ← checked <| parseHexBytes raw
  if bytes.size > maximum then fail "Paymaster RPC data exceeds its encoding bound."
  return bytes

private def poolForRequest (request : Request) : Except String Pool := do
  let row ← SelectedPoolBootstrap.byIdentity request.chainId request.pool
  let some chain := chainFromNat request.chainId | throw "Unsupported pool chain."
  let some pool := allPools.find? (fun pool => pool.chainId == chain &&
    (parseHexBytes pool.address).toOption.map wordNat == some row.address)
    | throw "Selected pool is outside the pinned catalog."
  return pool

def validateInput (input : Input) : Except String Pool := do
  if input.notes.isEmpty || input.notes.size > 12 || input.checkedBlock >= 2 ^ 64 ||
      input.maxBlockLag > 256 || input.maxFeeBps == 0 || input.maxFeeBps > 10000 then
    throw "Invalid paymaster preparation bounds."
  let first := input.notes[0]!
  let pool ← poolForRequest first
  let mut nullifiers := #[]
  let mut commitments := #[]
  for request in input.notes do
    request.validate
    let selected ← poolForRequest request
    if selected.chainId != pool.chainId || selected.asset != pool.asset ||
        nullifiers.contains request.nullifierHash || commitments.contains request.commitment then
      throw "Paymaster notes are duplicated or use different assets or chains."
    nullifiers := nullifiers.push request.nullifierHash
    commitments := commitments.push request.commitment
  match input.mode with
  | .single sender recipient =>
    if input.notes.size != 1 || sender == 0 || sender >= 2 ^ 160 ||
        recipient == 0 || recipient >= 2 ^ 160 || input.executionGasRetry then
      throw "Invalid direct one-note preparation scope."
  | .batch account receiver tail =>
    if input.notes.size == 1 && tail.isEmpty || account.address == 0 || account.owner == 0 ||
        account.address >= 2 ^ 160 || account.owner >= 2 ^ 160 ||
        receiver == 0 || receiver >= 2 ^ 160 || account.nonce >= 2 ^ 256 then
      throw "Invalid recoverable batch preparation scope."
    let _ ← Abi.validateCalls tail (some account.address)
    if !tail.isEmpty && receiver != account.address then
      throw "Post-withdrawal calls require the recoverable account as recipient."
    if input.tailCallGasEstimate.any (fun gas => gas == 0 || gas > input.bounds.maxCallGas) then
      throw "Invalid post-withdrawal execution gas estimate."
  return pool

/-- Exact alpha.38 baseline before bundler refinement. -/
def baselineGas (input : Input) (erc20 : Bool) (maximum priority : Nat) : Gas := {
  verification := match input.mode with
    | .batch account .. => if account.deployed then 50000 else 500000
    | .single .. => 50000
  execution := match input.mode with
    | .single .. => 0
    | .batch _ _ tail =>
      (input.notes.size - 1) * (if erc20 then 500000 else 400000) +
        (if tail.isEmpty then 60000 else input.tailCallGasEstimate.getD 300000)
  preVerification := 100000
  paymasterVerification := if erc20 then 550000 else 450000
  postOp := 50000
  maxFee := maximum
  priority }

private def gasOperation (sender nonce : Nat) (gas : Gas) : UserOperation := {
  sender, nonce, verificationGasLimit := gas.verification,
  callGasLimit := gas.execution, preVerificationGas := gas.preVerification,
  paymasterVerificationGasLimit := gas.paymasterVerification,
  paymasterPostOpGasLimit := gas.postOp, maxFeePerGas := gas.maxFee,
  maxPriorityFeePerGas := gas.priority }

private def priceReference (effects : Effects) : IO (Nat × Nat) := do
  try
    let history ← effects.rpc .feeHistory
      #[toJson ("0xa" : String), toJson ("latest" : String), toJson (#[90] : Array Nat)]
    if history.compress.utf8ByteSize > 4096 then fail "Oversized fee history."
    let rewards ← checked <| (← field history "reward").getArr?
    let bases ← checked <| (← field history "baseFeePerGas").getArr?
    if rewards.isEmpty || rewards.size > 10 || bases.size != rewards.size + 1 then
      fail "Invalid bounded fee history."
    let mut tip := 0
    for row in rewards do
      let percentiles ← checked row.getArr?
      if percentiles.size != 1 then fail "Invalid fee percentile row."
      tip := max tip (← quantity percentiles[0]!)
    return (← quantity bases[bases.size - 2]!, tip)
  catch _ =>
    let block ← effects.rpc .getBlockByNumber #[toJson ("latest" : String), toJson false]
    let base ← quantity (← field block "baseFeePerGas")
    let tip ← try quantity (← effects.rpc .maxPriorityFee #[]) catch _ => pure 0
    return (base, tip)

def checkPrice (maximum priority base referenceTip : Nat)
    (bounds : Bundler.Bounds := {}) : Except String Unit := do
  let tipCap := min 20000000000 (max 2000000000 (referenceTip * 3))
  let feeCap := base * 3 + tipCap
  if maximum == 0 || priority > maximum || priority > tipCap || maximum > feeCap ||
      maximum > bounds.maxFeePerGas then
    throw "Bundler gas prices exceed the host-reference bounds."

private def readPrice (effects : Effects) (bounds : Bundler.Bounds) : IO (Nat × Nat) := do
  let quote ← effects.bundler .pimlicoGasPrice #[]
  if quote.compress.utf8ByteSize > 4096 then fail "Oversized bundler gas price quote."
  let standard ← field quote "standard"
  let maximum ← quantity (← field standard "maxFeePerGas")
  let priority ← quantity (← field standard "maxPriorityFeePerGas")
  let (base, referenceTip) ← priceReference effects
  let _ ← checked <| checkPrice maximum priority base referenceTip bounds
  return (maximum, priority)

def requestsFor (input : Input) (fee : Nat) : Except String (Array Request) := do
  let pool ← validateInput input
  if fee == 0 || fee >= pool.amount || fee * 10000 > pool.amount * input.maxFeeBps then
    throw "Paymaster fee exceeds the reviewed sponsoring-note bound."
  let sponsor ← paymaster input.notes[0]!.chainId
  let recipient := match input.mode with
    | .single _ recipient => recipient
    | .batch account .. => account.address
  return input.notes.mapIdx fun index request => {
    request with
    recipient := recipient
    relayer := if index == 0 then sponsor else 0
    fee := if index == 0 then fee else 0
    refund := 0 }

/-- The SDK's fixed valid-shaped simulation proof; it is never a real proof
for a selected note. Its only permitted use is estimation with overrides. -/
def dummyProof : Except String ByteArray := do
  let twoX := 1368015179489954701390400359078579693043519447331113978918064868415326638035
  let twoY := 9918110051302171585080402603319702774565515993150576347155970296011118125764
  let coordinates := #[twoX, twoY,
    11559732032986387107991004021392285783925812861821192530917403151452391805634,
    10857046999023057135944570762232829481370756359578518086990519993285655852781,
    4082367875863433681332203403145435568316851327593401208105741076214120093531,
    8495653923123431417604973247489272438418190587263600148770280649306958101930,
    twoX, twoY]
  let mut bytes := ByteArray.empty
  for coordinate in coordinates do bytes := bytes ++ (← Abi.uintWord coordinate)
  return bytes

def dummySignature : Except String ByteArray :=
  parseHexBytes ("0xfffffffffffffffffffffffffffffff000000000000000000000000000000000" ++
    "7aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1c")

private def randomizedRequests (effects : Effects) (requests : Array Request) : IO (Array Request) := do
  let mut used := #[]
  let mut randomized := #[]
  for request in requests do
    let random ← effects.randomField
    if random >= BN254G1.scalarPrime ||
        requests.any (fun selected => selected.nullifierHash == random) || used.contains random then
      fail "Simulation nullifier must be a fresh canonical public field value."
    used := used.push random
    randomized := randomized.push { request with nullifierHash := random }
  return randomized

/-- A fixed dummy-only builder deliberately has no proof argument. -/
def simulationOperation (effects : Effects) (input : Input) (gas : Gas) (fee : Nat) : IO UserOperation := do
  let requests ← randomizedRequests effects (← checked <| requestsFor input fee)
  let first := requests[0]!
  let sponsor ← checked <| paymaster first.chainId
  let proof ← checked dummyProof
  let paymasterData ← checked <| Abi.sponsorParameters {
    instanceAddress := first.pool, proof,
    root := ← checked <| Abi.uintWord first.root,
    nullifierHash := ← checked <| Abi.uintWord first.nullifierHash,
    recipient := first.recipient, fee := first.fee }
  let baseOp ← match input.mode with
    | .single sender _ => pure <| gasOperation sender 0 gas
    | .batch account receiver tail => do
      let pool ← checked <| poolForRequest first
      let mut calls := #[]
      let mut total := 0
      for index in [0:requests.size] do
        let request := requests[index]!
        let selected ← checked <| poolForRequest request
        total := total + selected.amount
        if index > 0 then
          let callData ← checked <| Abi.poolWithdraw proof
            (← checked <| Abi.uintWord request.root)
            (← checked <| Abi.uintWord request.nullifierHash)
            request.recipient 0 0 0
          calls := calls.push { to := request.pool, value := 0, data := callData }
      calls := calls ++ tail
      if tail.isEmpty && receiver != account.address then
        match pool.asset.token with
        | none => calls := calls.push { to := receiver, value := total - fee, data := ByteArray.empty }
        | some raw =>
          let token := wordNat (← checked <| parseHexBytes raw)
          calls := calls.push {
            to := token
            value := 0
            data := ← checked <| Abi.erc20Transfer receiver (total - fee) }
      let factoryData ← if account.deployed then pure ByteArray.empty
        else checked <| Tornado.SmartAccount.accountFactoryData account.owner
      pure { gasOperation account.address account.nonce gas with
        callData := ← checked <| Abi.accountExecuteBatchComposed calls,
        factory := if account.deployed then none else
          some (.address 0x13e9ed32155810fdbd067d4522c492d6f68e5944), factoryData }
  let signature ← checked dummySignature
  let op := { baseOp with
    paymaster := some sponsor
    paymasterData := paymasterData
    signature := signature }
  let _ ← checked <| Bundler.validate op input.bounds
  return op

private def simulationJson (input : Input) (op : UserOperation) : Except String Json := do
  let json ← Bundler.encodeOperation op
  match input.mode with
  | .batch .. => return json
  | .single .. =>
    return json.setObjVal! "eip7702Auth" (Json.mkObj [
      ("address", toJson ("0xe6cae83bde06e4c305530e199d7217f42808555b" : String)),
      ("chainId", toJson (Bundler.quantity input.notes[0]!.chainId)),
      ("nonce", toJson ("0x0" : String)),
      ("r", toJson ("0xfffffffffffffffffffffffffffffff000000000000000000000000000000000" : String)),
      ("s", toJson ("0x7aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" : String)),
      ("yParity", toJson ("0x1" : String))])

private def verifierOverrides (effects : Effects) (input : Input) : IO Json := do
  let mut pools := #[]
  let mut verifiers := #[]
  for request in input.notes do
    unless pools.contains request.pool do
      pools := pools.push request.pool
      let result ← effects.rpc .call #[Json.mkObj [
        ("to", toJson (← checked <| Bundler.address request.pool)),
        ("data", toJson (Bundler.dataHex (Abi.selector "verifier()")))],
        toJson (Bundler.quantity input.checkedBlock)]
      let bytes ← data result 32
      if bytes.size != 32 || !(bytes.extract 0 12).data.all (· == 0) then
        fail "Invalid pool verifier address."
      let verifier := wordNat bytes
      if verifier == 0 then fail "Pool verifier address is zero."
      unless verifiers.contains verifier do verifiers := verifiers.push verifier
  let mut fields := []
  for index in [0:verifiers.size] do
    let verifier := verifiers[index]!
    let shadow := 0x4b6f68616b75 + index
    if verifiers.contains shadow || pools.contains shadow then
      fail "Simulation shadow address collides with a selected contract."
    let verifierText ← checked <| Bundler.address verifier
    let shadowText ← checked <| Bundler.address shadow
    let code ← data (← effects.rpc .getCode
      #[toJson verifierText, toJson (Bundler.quantity input.checkedBlock)]) 32768
    if code.isEmpty then fail "Selected pool verifier has no code."
    let forwarder := (← checked <| parseHexBytes "0x3660006000376000600036600073") ++
      ((← checked <| Abi.addressWord shadow).extract 12 32) ++
      (← checked <| parseHexBytes "0x5afa50600160005260206000f3")
    fields := fields ++ [
      (shadowText, Json.mkObj [("code", toJson (Bundler.dataHex code))]),
      (verifierText, Json.mkObj [("code", toJson (Bundler.dataHex forwarder))])]
  return Json.mkObj fields

private def quoteFee (effects : Effects) (input : Input) (pool : Pool) (gas : Gas) : IO Nat := do
  let ethFee := SponsoredWithdrawal.ethFee gas
  let fee ← match pool.asset.token with
    | none => pure ethFee
    | some raw => do
      let token := wordNat (← checked <| parseHexBytes raw)
      let sponsor ← checked <| paymaster input.notes[0]!.chainId
      let payload := Abi.selector "quoteWeiInToken(address,uint256)" ++
        (← checked <| Abi.addressWord token) ++ (← checked <| Abi.uintWord ethFee)
      let result ← effects.rpc .call #[Json.mkObj [
        ("to", toJson (← checked <| Bundler.address sponsor)),
        ("data", toJson (Bundler.dataHex payload))],
        toJson (Bundler.quantity input.checkedBlock)]
      let bytes ← data result 32
      if bytes.size != 32 then fail "Token fee quote is not one canonical word."
      pure <| wordNat bytes
  let _ ← checked <| requestsFor input fee
  return fee

private def assertGas (input : Input) (baseline current : Gas) (operation : UserOperation) : IO Unit := do
  let _ ← checked <| Bundler.validate operation input.bounds
  let direct := match input.mode with | .single .. => true | _ => false
  let verificationCap := if direct then min 250000 input.bounds.maxVerificationGas
    else min (baseline.verification * 2) input.bounds.maxVerificationGas
  let paymasterCap := if direct then input.bounds.maxPaymasterVerificationGas
    else min (baseline.paymasterVerification * 2) input.bounds.maxPaymasterVerificationGas
  let dataBytes := operation.callData.size + operation.paymasterData.size + operation.factoryData.size
  if current.verification > verificationCap || current.paymasterVerification > paymasterCap ||
      current.postOp > baseline.postOp * 2 ||
      current.preVerification > (350000 + 40 * dataBytes) * 2 ||
      (direct && current.execution != 0) then
    fail "Bundler gas estimates exceed the local preparation ceilings."

private def buffered (estimate : Nat) : Nat := (estimate * 12 + 9) / 10

def refineGas (current : Gas) (estimate : Bundler.GasEstimate) (direct : Bool) : Gas := {
  current with
  verification := max current.verification (buffered estimate.verificationGasLimit)
  execution := if direct then 0 else max current.execution (buffered estimate.callGasLimit)
  preVerification := max current.preVerification (buffered estimate.preVerificationGas)
  paymasterVerification := max current.paymasterVerification (buffered estimate.paymasterVerificationGasLimit)
  postOp := max current.postOp (buffered estimate.paymasterPostOpGasLimit) }

private def sameGas (a b : Gas) : Bool :=
  a.verification == b.verification && a.execution == b.execution &&
  a.preVerification == b.preVerification && a.paymasterVerification == b.paymasterVerification &&
  a.postOp == b.postOp && a.maxFee == b.maxFee && a.priority == b.priority

private def fallbackGas (current : Gas) (erc20 : Bool) (op : UserOperation) : Gas := {
  current with
  verification := max current.verification 150000
  paymasterVerification := max current.paymasterVerification (if erc20 then 1200000 else 650000)
  preVerification := max current.preVerification
    (300000 + (op.paymasterData.size - 512) * 40) }

private def freshHead (effects : Effects) (input : Input) : IO Unit := do
  if (← quantity (← effects.rpc .chainId #[])) != input.notes[0]!.chainId then
    fail "Paymaster RPC is on another network."
  let head ← quantity (← effects.rpc .blockNumber #[])
  if head < input.checkedBlock || head - input.checkedBlock > input.maxBlockLag then
    fail "Selected-pool public history is outside the allowed block freshness bound."

/-- Finite estimation runs without real proofs or owner signatures. Callback
errors are sanitized; only explicitly classified transport/internal outages
can use the conservative direct one-note fallback. -/
def estimateWith (effects : Effects) (input : Input) : IO Quote := do
  let pool ← checked <| validateInput input
  freshHead effects input
  effects.validateHistory input.notes
  let (maximum, priority) ← readPrice effects input.bounds
  let baseline := baselineGas input pool.asset.token.isSome maximum priority
  let overrides ← verifierOverrides effects input
  let cachedQuotes ← IO.mkRef (#[] : Array (Nat × Nat))
  let feeFor (gas : Gas) : IO Nat := do
    let ethFee := SponsoredWithdrawal.ethFee gas
    if let some (_, fee) := (← cachedQuotes.get).find? (fun (cost, _) => cost == ethFee) then
      return fee
    let fee ← quoteFee effects input pool gas
    cachedQuotes.modify (·.push (ethFee, fee))
    return fee
  let mut gas := baseline
  let mut attempts := 0
  let mut executionRetries := 0
  let direct := match input.mode with | .single .. => true | _ => false
  while attempts < 3 do
    let fee ← feeFor gas
    let operation ← simulationOperation effects input gas fee
    assertGas input baseline gas operation
    let json ← checked <| simulationJson input operation
    let params := #[json, toJson (← checked <| Bundler.address Bundler.entryPoint), overrides]
    let mut reply ← effects.estimate params
    if let .unavailable .transport := reply then reply ← effects.estimate params
    match reply with
    | .rejected => fail "Bundler rejected simulation; preparation stopped before real proofs."
    | .executionOutOfGas =>
      if !input.executionGasRetry || direct || executionRetries >= 3 ||
          gas.execution == 0 || gas.execution >= input.bounds.maxCallGas then
        fail "Execution gas estimation failed within the permitted retry bound."
      gas := { gas with execution := min input.bounds.maxCallGas (gas.execution * 2) }
      executionRetries := executionRetries + 1
    | .unavailable reason =>
      if !direct || input.policy != .bestEffort || executionRetries != 0 then
        fail "Required gas estimation is unavailable; preparation stopped."
      let fallback := fallbackGas gas pool.asset.token.isSome operation
      let finalFee ← feeFor fallback
      let fallbackOperation ← simulationOperation effects input fallback finalFee
      assertGas input baseline fallback fallbackOperation
      let requests ← checked <| requestsFor input finalFee
      return { input, gas := fallback, fee := finalFee, requests, estimation := .fallback reason }
    | .estimated raw =>
      let estimate ← checked <| Bundler.parseEstimate raw operation input.bounds
      let next := refineGas gas estimate direct
      if sameGas gas next then
        let requests ← checked <| requestsFor input fee
        return { input, gas, fee, requests, estimation := .estimated }
      let nextOperation := { operation with
        verificationGasLimit := next.verification, callGasLimit := next.execution,
        preVerificationGas := next.preVerification,
        paymasterVerificationGasLimit := next.paymasterVerification,
        paymasterPostOpGasLimit := next.postOp }
      assertGas input baseline next nextOperation
      gas := next
      attempts := attempts + 1
  fail "Paymaster gas estimates did not stabilize after three rounds."

/-- The real prover is called once per selected note, only after a stable
quote and a second live public-history check. Parent acceptance verifies the
exact six public inputs and proof under the compiled Classic key. -/
def prepareWith (effects : Effects) (input : Input) : IO Prepared := do
  let quote ← estimateWith effects input
  freshHead effects input
  effects.validateHistory quote.requests
  let notes ← quote.requests.mapM fun request => do
    let result ← try effects.prove request catch _ =>
      fail "Native proof worker failed after gas preparation."
    let _ ← checked <| ProverWorkerClient.acceptResponse request result
    return ({ request, result } : NoteProof)
  return { quote, notes }

end Tornado.Cli.PaymasterPrepare
