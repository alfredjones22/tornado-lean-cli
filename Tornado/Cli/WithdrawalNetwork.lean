import Tornado.Cli.PaymasterPrepare
import Tornado.Protocol.EntryPointSimulation

/-! Bounded native network adapters for experimental sponsored preparation
and signed batch simulation. Dummy estimates have their own typed outcome;
signed simulation is never retried. Every caller must durably reserve a signed
candidate before invoking `simulate`. These checks validate provider claims,
not Ethereum consensus. The explicit send callback submits at most one attempt
per signed payload after the caller's durable reservation. -/

namespace Tornado.Cli.WithdrawalNetwork

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli.PaymasterPrepare

structure Settings where
  chainId : Nat
  rpcUrl : String
  bundlerUrl : String
  simulationRpcUrl : Option String := none
  customBundler : Bool := false
  simulationPolicy : PaymasterPrepare.Policy := .required
  deriving Inhabited

structure Transport where
  call : String → Nat → JsonRpc.Method → Array Json → IO JsonRpc.Reply
  nowMs : IO Nat
  sleepMs : Nat → IO Unit := fun ms => IO.sleep ms.toUInt32

structure Client where
  rpc : JsonRpc.Method → Array Json → IO Json
  bundler : JsonRpc.Method → Array Json → IO Json
  send : JsonRpc.Method → Array Json → IO Json
  estimate : Array Json → IO PaymasterPrepare.EstimateReply
  simulate : UserOperation → List Events.ExpectedWithdrawal → PaymasterPrepare.Estimation → Bundler.Bounds → IO Bool
  checkChain : IO Unit
  blockNumber : IO Nat
  nonce : Nat → IO Nat
  revalidateGasPrice : SponsoredWithdrawal.Gas → IO Unit
  /-- Pre-review only, for routes without arbitrary post-withdrawal calls. -/
  refreshGasBidDownward : SponsoredWithdrawal.Gas → Bundler.Bounds → IO SponsoredWithdrawal.Gas

private def fail : IO α := throw <| IO.userError "Withdrawal network request failed or was rejected."

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => fail

private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def aaCode (message : String) (expected : Option Nat := none) : Bool := Id.run do
  let chars := message.toUpper.toList.toArray
  for i in [0:chars.size] do
    if i + 3 < chars.size && chars[i]! == 'A' && chars[i + 1]! == 'A' &&
        chars[i + 2]!.isDigit && chars[i + 3]!.isDigit then
      let value := (chars[i + 2]!.toNat - '0'.toNat) * 10 + chars[i + 3]!.toNat - '0'.toNat
      if expected.isNone || expected == some value then return true
  return false

private def errorHasData (data : Option Json) : Bool :=
  match data with
  | none | some .null => false
  | some _ => true

private def explicitFailure (message : String) : Bool :=
  let text := message.toLower
  aaCode message || has text "revert" || has text "failedop" ||
    has text "failed op" || has text "out of gas" || has text "out-of-gas"

/-- Classify only the fixed transport diagnostic emitted by the C binding.
Other IO errors (TLS failure, size bound, malformed envelope or file error)
never become an unavailable simulation or successful preparation. -/
def transportUnavailable (error : IO.Error) : Bool :=
  match error with
  | .userError message => message == "HTTPS transport unavailable"
  | _ => false

private def hexDigit (char : Char) : Bool :=
  ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f')

/-- Recognize exactly a nonzero ABI-encoded CallGasLimitNonZero(uint256)
token. Truncated/extended words, zero arguments and embedded selector text
cannot downgrade an arbitrary validation failure into availability. -/
private def nonzeroCallGasRevert (message : String) : Bool := Id.run do
  let chars := message.toLower.toList.toArray
  for index in [0:chars.size] do
    if index > 0 && (chars[index - 1]!.isAlphanum || chars[index - 1]! == '_') then continue
    if index + 74 > chars.size then continue
    let token := String.ofList (chars.extract index (index + 74)).toList
    if !token.startsWith "0x54107e37" then continue
    let word := String.ofList (token.toList.drop 10)
    if !word.toList.all hexDigit || word.toList.all (· == '0') then continue
    if index + 74 < chars.size && hexDigit chars[index + 74]! then continue
    return true
  return false

private def validationOnlyEstimate (params : Array Json) : Bool :=
  params.size == 3 && params[0]?.any (fun operation =>
    ((operation.getObjVal? "callData").bind Json.getStr?).toOption == some "0x" &&
    ((operation.getObjVal? "callGasLimit").bind Json.getStr?).toOption == some "0x0")

/-- Validation failures remain rejection except the SDK's known estimator
incompatibility: AA33 + exact nonzero CallGasLimitNonZero for an operation
whose calldata and execution limit are both empty/zero. Direct-single
preparation can automatically consume only this known-incompatibility result;
all other outages retain their separate policy and eligibility gates. -/
def classifyEstimate (reply : JsonRpc.Reply) (params : Array Json := #[]) : PaymasterPrepare.EstimateReply :=
  match reply with
  | .success result => .estimated result
  | .failure code message data =>
    let lower := message.toLower
    if code == -32501 && !errorHasData data && aaCode message (some 33) &&
        validationOnlyEstimate params && nonzeroCallGasRevert message then
      .unavailable .validationOnlyEstimator
    else if !errorHasData data && code == -32521 && aaCode message (some 95) &&
        has lower "execution" && (has lower "out of gas" || has lower "out-of-gas") then
      .executionOutOfGas
    else if code == -32603 && !errorHasData data && !explicitFailure message then
      .unavailable .bundlerInternal
    else .rejected

private def successful (reply : JsonRpc.Reply) : IO Json :=
  match reply with
  | .success value => pure value
  | .failure .. => fail

private def quantity (value : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked value.getStr?)

private def field (value : Json) (name : String) : IO Json :=
  checked <| value.getObjVal? name

private def allowedRead (method : JsonRpc.Method) : Bool :=
  [JsonRpc.Method.chainId, .blockNumber, .getBlockByNumber, .getCode, .getBalance,
    .getStorageAt, .getTransactionCount, .call, .feeHistory, .maxPriorityFee,
    .getLogs, .getTransactionByHash, .getTransactionReceipt].contains method

private def checkSettings (settings : Settings) : IO Unit := do
  if (settings.chainId != 1 && settings.chainId != 11155111) ||
      !HttpTransport.validRpcUrl settings.rpcUrl ||
      !HttpTransport.validRpcUrl settings.bundlerUrl ||
      settings.simulationRpcUrl.any (fun url => !HttpTransport.validRpcUrl url) then fail

private def dummyEstimate (params : Array Json) : Except String Unit := do
  if params.size != 3 || params[0]!.compress.utf8ByteSize > Bundler.maxOperationBytes ||
      params[2]!.compress.utf8ByteSize > 512 * 1024 then
    throw "Invalid dummy estimate bounds."
  if (← params[1]!.getStr?).toLower != (← Bundler.address Bundler.entryPoint) then
    throw "Unexpected dummy estimate EntryPoint."
  let operation := params[0]!
  let signature ← (← operation.getObjVal? "signature").getStr?
  if signature != Bundler.dataHex (← PaymasterPrepare.dummySignature) then
    throw "Gas estimation requires the fixed dummy signature."
  let sponsorData ← (← operation.getObjVal? "paymasterData").getStr?
  let sponsor ← Abi.decodeSponsorParameters (← parseHexBytes sponsorData)
  if sponsor.proof != (← PaymasterPrepare.dummyProof) then
    throw "Gas estimation requires the fixed dummy proof."
  if let .ok auth := operation.getObjVal? "eip7702Auth" then
    if (← (← auth.getObjVal? "r").getStr?) !=
        "0xfffffffffffffffffffffffffffffff000000000000000000000000000000000" ||
        (← (← auth.getObjVal? "s").getStr?) !=
        "0x7aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ||
        (← (← auth.getObjVal? "yParity").getStr?) != "0x1" then
      throw "Gas estimation requires a dummy authorization."

private def hostReference (read : JsonRpc.Method → Array Json → IO Json) : IO (Nat × Nat) := do
  try
    let history ← read .feeHistory
      #[toJson ("0xa" : String), toJson ("latest" : String), toJson (#[90] : Array Nat)]
    let rewards ← checked <| (← field history "reward").getArr?
    let bases ← checked <| (← field history "baseFeePerGas").getArr?
    if rewards.isEmpty || rewards.size > 10 || bases.size != rewards.size + 1 then fail
    let mut tip := 0
    for row in rewards do
      let values ← checked row.getArr?
      if values.size != 1 then fail
      tip := max tip (← quantity values[0]!)
    return (← quantity bases[bases.size - 2]!, tip)
  catch _ =>
    let block ← read .getBlockByNumber #[toJson ("latest" : String), toJson false]
    let base ← quantity (← field block "baseFeePerGas")
    let tip ← try quantity (← read .maxPriorityFee #[]) catch _ => pure 0
    return (base, tip)

private def gasReferenceUnavailable : IO α :=
  throw <| IO.userError
    "Could not refresh network gas prices. Check --rpc or try another endpoint."

private def diagnosticNat (value : Nat) : String :=
  if value < 2 ^ 256 then toString value else "at least 2^256"

private def gasPriceDetails (gas : SponsoredWithdrawal.Gas) (base tip : Nat) : String :=
  s!" Fees in wei/gas: current base {diagnosticNat base}; reference priority {diagnosticNat tip}; prepared maxFee {diagnosticNat gas.maxFee}; prepared priority {diagnosticNat gas.priority}."

/-- A bid refresh changes only prices, never gas limits or the proved fee.
The caller still checks the resulting bid against fresh host price evidence. -/
def acceptDownwardGas (original candidate : SponsoredWithdrawal.Gas)
    (bounds : Bundler.Bounds := {}) : Except String SponsoredWithdrawal.Gas := do
  if candidate.verification != original.verification || candidate.execution != original.execution ||
      candidate.preVerification != original.preVerification ||
      candidate.paymasterVerification != original.paymasterVerification || candidate.postOp != original.postOp then
    throw "Gas refresh changed a prepared gas limit."
  if candidate.maxFee > original.maxFee || candidate.priority > original.priority then
    throw "Gas refresh would increase a prepared price. Obtain a new withdrawal quote."
  let operation : UserOperation := {
    sender := 1, paymaster := some 1,
    verificationGasLimit := candidate.verification, callGasLimit := candidate.execution,
    preVerificationGas := candidate.preVerification,
    paymasterVerificationGasLimit := candidate.paymasterVerification,
    paymasterPostOpGasLimit := candidate.postOp, maxFeePerGas := candidate.maxFee,
    maxPriorityFeePerGas := candidate.priority }
  if !(Bundler.validate operation bounds).isOk then
    throw "Refreshed gas bid exceeds its configured limits."
  return candidate

/-- Keeping all limits and lowering maxFee cannot increase the native ETH
prefund quote; priority changes do not enter that maximum-cost calculation. -/
theorem lowerGasBid_ethFee_nonincreasing (original : SponsoredWithdrawal.Gas)
    (maximum priority : Nat) (h : maximum ≤ original.maxFee) :
    SponsoredWithdrawal.ethFee { original with maxFee := maximum, priority } ≤
      SponsoredWithdrawal.ethFee original := by
  dsimp [SponsoredWithdrawal.ethFee]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right 120 (Nat.mul_le_mul_left _ h))

/-- Custom bundlers use only the selected host's bounded EIP-1559 reference,
with twice its base and tip allowance. No third-party gas oracle is consulted. -/
def customPrice (read : JsonRpc.Method → Array Json → IO Json) : IO Json := do
  let (base, tip) ← hostReference read
  let priority := tip * 2
  let maximum := base * 2 + priority
  if maximum == 0 || maximum >= 2 ^ 256 || priority >= 2 ^ 256 then fail
  let tier := Json.mkObj [
    ("maxFeePerGas", toJson (Bundler.quantity maximum)),
    ("maxPriorityFeePerGas", toJson (Bundler.quantity priority))]
  return Json.mkObj [("slow", tier), ("standard", tier), ("fast", tier)]

private def unsupportedSimulation (reply : JsonRpc.Reply) : Bool :=
  match reply with
  | .failure code message data =>
    [-32601, -32004, 4200].contains code && !errorHasData data && !explicitFailure message
  | _ => false

private def admitUnavailable (policy : PaymasterPrepare.Policy)
    (prior : PaymasterPrepare.Estimation) : Bool :=
  policy == .bestEffort && prior == .estimated

/-- Stateful, injected adapter. Request IDs are fresh across every endpoint.
Each signed operation hash is simulated at most once; even an unavailable
response consumes that exposure slot. Remote errors never reach a terminal. -/
def createWith (settings : Settings) (transport : Transport) : IO Client := do
  checkSettings settings
  let nextId ← IO.mkRef (1 : Nat)
  let attemptedSimulations ← IO.mkRef (#[] : Array ByteArray)
  let attemptedSends ← IO.mkRef (#[] : Array ByteArray)
  let reply (url : String) (method : JsonRpc.Method) (params : Array Json) : IO JsonRpc.Reply := do
    let id ← nextId.get
    if id > 8192 then fail
    nextId.set (id + 1)
    let encoded ← checked <| JsonRpc.encodeRequest id method params
    if encoded.utf8ByteSize > 1024 * 1024 then fail
    let response ← transport.call url id method params
    match response with
    | .success value => if value.compress.utf8ByteSize > 1024 * 1024 then fail
    | .failure _ message data =>
      if message.utf8ByteSize > 4096 ||
          data.any (fun value => value.compress.utf8ByteSize > 65536) then fail
    return response
  let read (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    unless allowedRead method do fail
    try successful (← reply settings.rpcUrl method params) catch _ => fail
  let checkChain : IO Unit := do
    if (← quantity (← read .chainId #[])) != settings.chainId then fail
  let getBlock : IO Nat := do
    let block ← quantity (← read .blockNumber #[])
    if block >= 2 ^ 64 then fail
    return block
  let getNonce (owner : Nat) : IO Nat := do
    let nonce ← quantity (← read .getTransactionCount
      #[toJson (← checked <| Bundler.address owner), toJson ("latest" : String)])
    if nonce >= 2 ^ 64 - 1 then fail
    return nonce
  let gasReference : IO (Nat × Nat) := do
    let retries ← IO.mkRef (0 : Nat)
    let gasRead (method : JsonRpc.Method) (params : Array Json) : IO Json := do
      unless [JsonRpc.Method.feeHistory, .getBlockByNumber, .maxPriorityFee].contains method do
        gasReferenceUnavailable
      for _ in [0:3] do
        let attempt ← try
            pure (.ok (← reply settings.rpcUrl method params) : Except IO.Error JsonRpc.Reply)
          catch error => pure (.error error)
        match attempt with
        | .ok (.success value) => return value
        | .ok (.failure ..) => gasReferenceUnavailable
        | .error error =>
          if !transportUnavailable error then gasReferenceUnavailable
          let used ← retries.get
          if used >= 2 then gasReferenceUnavailable
          retries.set (used + 1)
          transport.sleepMs (if used == 0 then 500 else 1000)
      gasReferenceUnavailable
    try hostReference gasRead catch _ => gasReferenceUnavailable
  return {
    rpc := read
    checkChain := checkChain
    blockNumber := getBlock
    nonce := getNonce
    revalidateGasPrice := fun gas => do
      let (base, tip) ← gasReference
      if !(PaymasterPrepare.checkPrice gas.maxFee gas.priority base tip).isOk then
        throw <| IO.userError
          ("Prepared gas quote exceeds current network price limits. Run the withdrawal again for a fresh quote." ++
            gasPriceDetails gas base tip)
      if gas.maxFee < base + gas.priority then
        throw <| IO.userError
          ("Prepared max fee no longer covers the current base fee and priority fee. Run the withdrawal again for a fresh quote." ++
            gasPriceDetails gas base tip)
    refreshGasBidDownward := fun original bounds => do
      let quote ← if settings.customBundler then pure none else
        try some <$> successful (← reply settings.bundlerUrl .pimlicoGasPrice #[])
        catch _ => throw <| IO.userError "Could not refresh the bundler gas quote. Check --bundler-url or try again."
      let (base, tip) ← gasReference
      let (maximum, priority) ← match quote with
        | none => pure (base * 2 + tip * 2, tip * 2)
        | some value => try
            if value.compress.utf8ByteSize > 4096 then fail
            let standard ← field value "standard"
            pure (← quantity (← field standard "maxFeePerGas"),
              ← quantity (← field standard "maxPriorityFeePerGas"))
          catch _ => throw <| IO.userError "The fresh bundler gas quote is malformed. Check --bundler-url or try another bundler."
      if !(PaymasterPrepare.checkPrice maximum priority base tip bounds).isOk then
        throw <| IO.userError "The fresh bundler gas quote exceeds current price limits. Try another bundler or obtain a new withdrawal quote."
      if priority > original.priority then
        throw <| IO.userError "The current recommended priority fee exceeds the prepared bid. Obtain a new withdrawal quote."
      let tipCap := min 20000000000 (max 2000000000 (tip * 3))
      let maximum := if base < 1000000 then
          min (maximum + 1000000) (min (base * 3 + tipCap) bounds.maxFeePerGas)
        else maximum
      let candidate := { original with maxFee := min original.maxFee maximum, priority }
      let candidate ← match acceptDownwardGas original candidate bounds with
        | .ok gas => pure gas
        | .error message => throw <| IO.userError message
      if !(PaymasterPrepare.checkPrice candidate.maxFee candidate.priority base tip bounds).isOk ||
          candidate.maxFee < base + candidate.priority then
        throw <| IO.userError
          ("A current gas bid cannot fit the prepared budget. Obtain a new withdrawal quote." ++
            gasPriceDetails candidate base tip)
      return candidate
    send := fun method params => do
      if method != .sendUserOperation || params.size != 2 then fail
      let entryPoint ← checked <| params[1]!.getStr?
      if entryPoint.toLower != (← checked <| Bundler.address Bundler.entryPoint) then fail
      let body := (Json.arr params).compress.toUTF8
      if body.size > Bundler.maxOperationBytes + 128 then fail
      let hash := keccak256 body
      if (← attemptedSends.get).contains hash then fail
      checkChain
      attemptedSends.modify (·.push hash)
      try successful (← reply settings.bundlerUrl method params) catch _ => fail
    bundler := fun method params => do
      if method != .pimlicoGasPrice || !params.isEmpty then fail
      try
        if settings.customBundler then customPrice read
        else successful (← reply settings.bundlerUrl method params)
      catch _ => fail
    estimate := fun params => do
      if !(dummyEstimate params).isOk then return .rejected
      try
        return classifyEstimate (← reply settings.bundlerUrl .estimateUserOperationGas params) params
      catch error =>
        if transportUnavailable error then return .unavailable .transport
        return .rejected
    simulate := fun operation expected prior bounds => do
      let hash ← match userOperationHash settings.chainId Bundler.entryPoint operation with
        | .ok hash => pure hash
        | .error _ => return false
      if (← attemptedSimulations.get).contains hash then return false
      attemptedSimulations.modify (·.push hash)
      let params ← match EntryPointSimulation.requestParams operation bounds with
        | .ok params => pure params
        | .error _ => return false
      let endpoint := settings.simulationRpcUrl.getD settings.rpcUrl
      try
        let network ← successful (← reply endpoint .chainId #[])
        if (← quantity network) != settings.chainId then return false
        let response ← reply endpoint .simulateV1 params
        match response with
        | .success result =>
          return (EntryPointSimulation.parsePassed settings.chainId operation expected result).isOk
        | .failure .. =>
          return unsupportedSimulation response && admitUnavailable settings.simulationPolicy prior
      catch error =>
        return transportUnavailable error && admitUnavailable settings.simulationPolicy prior }

def native (settings : Settings) : IO Client :=
  createWith settings { call := HttpTransport.callReply, nowMs := IO.monoMsNow }

def Client.preparationEffects (client : Client) (randomField : IO Nat)
    (prove : ProverWorkerWire.Request → IO ProverWorkerWire.Result)
    (validateHistory : Array ProverWorkerWire.Request → IO Unit) : PaymasterPrepare.Effects := {
  rpc := client.rpc, bundler := client.bundler, estimate := client.estimate,
  randomField, prove, validateHistory }

end Tornado.Cli.WithdrawalNetwork

#print axioms Tornado.Cli.WithdrawalNetwork.lowerGasBid_ethFee_nonincreasing
