import Tornado.Runtime.WithdrawalJournalProgram
import Tornado.Cli.RelayerWithdrawalStatus
import Tornado.Protocol.SponsoredWithdrawal
import Tornado.Policy

/-!
Classic relayer discovery, quote validation and explicitly experimental
one-POST submission using the isolated variable-time Lean prover.
Provider responses are checked claims, not authenticated chain consensus.
-/

namespace Tornado.Cli.RelayerSend

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime

def maxRpcBytes : Nat := 1024 * 1024
def maxStatusBytes : Nat := 65536
def maxRegistryEvents : Nat := 2048
def maxRegistryCandidates : Nat := 256
def maxRelayerChecks : Nat := 64
def minStake : Nat := 40 * 10 ^ 18
def withdrawGas : Nat := 550000
def maxGasPrice : Nat := 1000 * 10 ^ 9
def quoteLifetimeMs : Nat := 5 * 60 * 1000

private def invalid : String := "Invalid Classic relayer data or withdrawal review."
private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => throw <| IO.userError invalid
private def fail : IO α := throw <| IO.userError invalid
private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def text (value : Json) (name : String) : Except String String := do
  (← field value name).getStr?
private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
private def word (value : Nat) : Except String ByteArray := Abi.uintWord value
private def hexText (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes
private def quantity (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)
private def addressText (value : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:20] do bytes := bytes.push ((value / 256 ^ (19 - i) % 256).toUInt8)
  return hexText bytes

private def bytes (raw : String) (size : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" || raw.length != size * 2 + 2 then throw invalid
  let value ← parseHexBytes raw
  if value.size != size then throw invalid
  return value

private def address (raw : String) : Except String Nat := do
  let value := wordNat (← bytes raw 20)
  if value == 0 then throw invalid
  return value

private def canonicalClassicPool (pool : Pool) : Bool :=
  match poolFor pool.chainId pool.denomination pool.asset.symbol with
  | none => false
  | some known => known.classicRelayer && pool.classicRelayer &&
      known.address.toLower == pool.address.toLower &&
      pool.amount == known.amount && pool.asset == known.asset

private def asciiAlphaNum (c : Char) : Bool :=
  ('a' <= c && c <= 'z') || ('0' <= c && c <= '9')
private def labelValid (value : String) : Bool :=
  !value.isEmpty && value.length <= 63 && !value.startsWith "-" &&
  !value.endsWith "-" && value.toList.all (fun c => asciiAlphaNum c || c == '-')

/-- Conservative ASCII ENS subset. Unsupported Unicode names fail closed. -/
def namehash (name : String) : Except String ByteArray := do
  if !name.toList.all (fun c => c.toNat < 128) then throw invalid
  let normalized := name.toLower
  let labels := normalized.splitOn "."
  if normalized.length > 255 || labels.length < 2 || labels.getLast! != "eth" ||
      !labels.all labelValid then throw invalid
  let mut node : ByteArray := ⟨Array.replicate 32 0⟩
  for label in labels.reverse do node := keccak256 (node ++ keccak256 label.toUTF8)
  return node

/-- Canonical HTTPS origin with an ASCII DNS hostname and no credentials,
    port, path, query, fragment, local suffix, or numeric IP literal. -/
def relayerUrl (raw : String) : Except String String := do
  if !raw.startsWith "https://" || raw.length > 512 then throw invalid
  let rest := String.ofList (raw.toList.drop 8)
  let host := if rest.endsWith "/" then String.ofList rest.toList.dropLast else rest
  if host.length > 253 || !host.toList.all (fun c => c.toNat < 128) then throw invalid
  let host := host.toLower
  let labels := host.splitOn "."
  if labels.length < 2 || !labels.all labelValid ||
      host.endsWith ".local" || host.endsWith ".internal" ||
      labels.getLast!.toList.all Char.isDigit then throw invalid
  return "https://" ++ host ++ "/"

structure Config where
  registry : Nat
  registryDeployment : Nat
  aggregator : Nat
  subdomains : Array String

def config (chainId : Nat) : Except String Config :=
  if chainId == 1 then
    .ok ⟨0x58e8dcc13be9780fc42e8723d8ead4cf46943df2, 0xd843c9,
      0xe8f47a78a6d52d317d0d2fffac56739fe14d1b49, #["mainnet-tornado"]⟩
  else if chainId == 11155111 then
    .ok ⟨0xd6663593e71e4916ecb6f6606e1a6fbfa1634ffa, 0x555e24,
      0x4088712ac9fad39ea133cdb9130e465d235e9642,
      #["mainnet-tornado", "sepolia-tornado"]⟩
  else .error invalid

private def atWord (data : ByteArray) (offset : Nat) : Except String Nat := do
  if offset + 32 > data.size then throw invalid
  return wordNat (data.extract offset (offset + 32))
private def dynamicString (value : String) : Except String ByteArray := do
  let raw := value.toUTF8
  if raw.size > 512 then throw invalid
  return (← word raw.size) ++ raw ++
    ⟨Array.replicate ((32 - raw.size % 32) % 32) 0⟩
private def atString (data : ByteArray) (offset : Nat) : Except String String := do
  let size ← atWord data offset
  if size > 512 || offset + 32 + size > data.size then throw invalid
  let some value := String.fromUTF8? (data.extract (offset + 32) (offset + 32 + size))
    | throw invalid
  return value

def aggregatorCall (node : ByteArray) (subdomains : Array String) : Except String ByteArray := do
  if node.size != 32 || subdomains.isEmpty || subdomains.size > 2 then throw invalid
  let mut offsets := ByteArray.empty
  let mut strings := ByteArray.empty
  for value in subdomains do
    offsets := offsets ++ (← word (32 * subdomains.size + strings.size))
    strings := strings ++ (← dynamicString value)
  return Abi.selector "relayersData(bytes32[],string[])" ++
    (← word 64) ++ (← word 128) ++ (← word 1) ++ node ++
    (← word subdomains.size) ++ offsets ++ strings

structure Registration where
  owner : Nat
  stake : Nat
  registered : Bool
  records : Array String
  deriving Inhabited

def encodeRegistration (value : Registration) : Except String ByteArray := do
  if value.owner >= 2 ^ 160 || value.records.size != 20 then throw invalid
  let mut offsets := ByteArray.empty
  let mut strings := ByteArray.empty
  for value in value.records do
    offsets := offsets ++ (← word (640 + strings.size))
    strings := strings ++ (← dynamicString value)
  return (← word 32) ++ (← word 1) ++ (← word 32) ++
    (← word value.owner) ++ (← word value.stake) ++
    (← word (if value.registered then 1 else 0)) ++ (← word 128) ++ offsets ++ strings

/-- Exact canonical re-encoding rejects offset tricks, trailing bytes and
    malformed bools; one ENS name is looked up per aggregator request. -/
def decodeRegistration (data : ByteArray) : Except String Registration := do
  if data.size > 16384 || (← atWord data 0) != 32 ||
      (← atWord data 32) != 1 || (← atWord data 64) != 32 ||
      (← atWord data 192) != 128 then throw invalid
  let owner ← atWord data 96
  let stake ← atWord data 128
  let registered ← atWord data 160
  if owner >= 2 ^ 160 || registered > 1 then throw invalid
  let mut records := #[]
  for i in [0:20] do
    let offset ← atWord data (224 + i * 32)
    if offset % 32 != 0 || offset < 640 then throw invalid
    records := records.push (← atString data (224 + offset))
  let value : Registration := ⟨owner, stake, registered == 1, records⟩
  if (← encodeRegistration value) != data then throw invalid
  return value

structure RegistryEvent where
  ensName : String
  owner : Nat
  block : Nat
  logIndex : Nat
  deriving Inhabited

def registryTopic : ByteArray :=
  keccak256 "RelayerRegistered(bytes32,string,address,uint256)".toUTF8

def decodeRegistryEvent (cfg : Config) (fromBlock toBlock : Nat)
    (json : Json) : Except String RegistryEvent := do
  if (← address (← text json "address")) != cfg.registry then throw invalid
  let block ← JsonRpc.parseHexQuantity (← text json "blockNumber")
  let logIndex ← JsonRpc.parseHexQuantity (← text json "logIndex")
  if block < fromBlock || block > toBlock || block >= 2 ^ 64 || logIndex >= 2 ^ 32 then throw invalid
  if let .ok removed := field json "removed" then
    if (← removed.getBool?) then throw invalid
  let _ ← bytes (← text json "transactionHash") 32
  let _ ← bytes (← text json "blockHash") 32
  let topics ← (← field json "topics").getArr?
  if topics.size != 1 || (← bytes (← topics[0]!.getStr?) 32) != registryTopic then throw invalid
  let raw ← text json "data"
  if raw.length > 2048 then throw invalid
  let data ← parseHexBytes raw
  if (← atWord data 32) != 128 then throw invalid
  let owner ← atWord data 64
  let stake ← atWord data 96
  if owner == 0 || owner >= 2 ^ 160 then throw invalid
  let ensName ← atString data 128
  let node ← namehash ensName
  let expected := node ++ (← word 128) ++ (← word owner) ++
    (← word stake) ++ (← dynamicString ensName)
  if expected != data then throw invalid
  return ⟨ensName.toLower, owner, block, logIndex⟩

structure Relayer where
  ensName : String
  url : String
  rewardAccount : Nat
  stake : Nat
  serviceFeeBps : Nat
  tokenPrice : Option Nat
  deriving Inhabited

private def serviceBps (json : Json) : Except String Nat := do
  let number ← json.getNum?
  if number.exponent > 12 || number.mantissa <= 0 || number.mantissa > 10 ^ 12 then throw invalid
  let numerator := number.mantissa.toNat
  let denominator := 10 ^ number.exponent
  if numerator * 100 < denominator || numerator >= denominator then throw invalid
  let result := (numerator * 200 + denominator) / (2 * denominator)
  if result == 0 || result >= 100 then throw invalid
  return result

private def priceValue (raw : String) : Except String Nat := do
  if raw.length > 78 || raw.isEmpty then throw invalid
  let value ← if raw.startsWith "0x" then JsonRpc.parseHexQuantity raw else do
    let some value := raw.toNat? | throw invalid
    if toString value != raw then throw invalid
    pure value
  if value == 0 || value >= 2 ^ 256 then throw invalid
  return value

def checkStatus (pool : Pool) (registration : RegistryEvent)
    (data : Registration) (raw : ByteArray) : Except String Relayer := do
  if !canonicalClassicPool pool || raw.size > maxStatusBytes ||
      !data.registered || data.stake < minStake || data.owner != registration.owner ||
      data.records.size != 20 || data.records[0]!.isEmpty then throw invalid
  let cfg ← config (chainNumber pool.chainId)
  let hostname := data.records[cfg.subdomains.size - 1]!
  let url ← relayerUrl ("https://" ++ hostname ++ "/")
  let some rawText := String.fromUTF8? raw | throw invalid
  let json ← Json.parse rawText
  if (← (← field json "netId").getNat?) != chainNumber pool.chainId ||
      (← (← field json "currentQueue").getNat?) > 5 ||
      (← address (← text json "rewardAccount")) != data.owner then throw invalid
  let version ← text json "version"
  if version.isEmpty || version.length > 128 then throw invalid
  let bps ← serviceBps (← field json "tornadoServiceFee")
  let pools ← field (← field (← field json "instances") pool.asset.symbol.toLower) "instanceAddress"
  let poolEntries ← pools.getObj?
  if poolEntries.size > 64 || !(poolEntries.toList.any (fun (_, value) =>
      match value.getStr? >>= address with
      | .error _ => false
      | .ok value => value == (address pool.address).toOption.getD 0)) then throw invalid
  let tokenPrice ← match pool.asset.token with
    | none => pure none
    | some _ => do
      let prices ← field json "ethPrices"
      let value := (field prices pool.asset.symbol.toLower).toOption.orElse
        (fun _ => (field prices pool.asset.symbol.toUpper).toOption) |>.orElse
        (fun _ => (field prices pool.asset.symbol).toOption)
      let some value := value | throw invalid
      let price ← priceValue (← value.getStr?)
      pure (some price)
  return ⟨registration.ensName, url, data.owner, data.stake, bps, tokenPrice⟩

structure Amounts where
  fee : Nat
  net : Nat
  serviceFee : Nat
  networkFee : Nat
  deriving BEq, Inhabited

/-- Token quotes require a separately configured paymaster TWAP reference;
    a relayer-supplied price cannot increase the fee more than 20% above it. -/
def quoteAmounts (pool : Pool) (relayer : Relayer) (gasPrice : Nat)
    (referenceNetworkFee : Option Nat) : Except String Amounts := do
  if !canonicalClassicPool pool || gasPrice == 0 || gasPrice > maxGasPrice then throw invalid
  let networkWei := gasPrice * withdrawGas
  let networkFee ← match pool.asset.token with
    | none => pure networkWei
    | some _ => do
      let some price := relayer.tokenPrice | throw invalid
      let some reference := referenceNetworkFee | throw invalid
      if price == 0 || reference == 0 || reference >= pool.amount then throw invalid
      let value := networkWei * 10 ^ pool.asset.decimals / price
      if value * 10000 > reference * 12000 then throw invalid
      pure value
  let fee := networkFee + pool.amount * relayer.serviceFeeBps / 10000
  let some result := Tornado.Policy.validateRelayerFee
    ⟨pool.amount, fee, relayer.serviceFeeBps⟩ | throw invalid
  return ⟨result.fee, result.net, result.serviceFee, result.networkFee⟩

structure Effects where
  rpc : JsonRpc.Method → Array Json → IO Json
  get : String → IO ByteArray
  nowMs : IO Nat

private def boundedEffects (source : Effects) : IO Effects := do
  let started ← source.nowMs
  let calls ← IO.mkRef (0 : Nat)
  let totalBytes ← IO.mkRef (0 : Nat)
  let admitRequest : IO Unit := do
    let now ← source.nowMs
    if now < started || now - started > 300000 then fail
    let count ← calls.get
    if count >= 8192 then fail
    calls.set (count + 1)
  let account (size : Nat) : IO Unit := do
    let total ← totalBytes.get
    if total + size > 64 * 1024 * 1024 then fail
    totalBytes.set (total + size)
    let now ← source.nowMs
    if now < started || now - started > 300000 then fail
  return {
    rpc := fun method params => do
      admitRequest
      let value ← source.rpc method params
      account value.compress.toUTF8.size
      return value,
    get := fun url => do
      admitRequest
      let value ← source.get url
      if value.size > maxStatusBytes then fail
      account value.size
      return value,
    nowMs := source.nowMs }

private def rpc (effects : Effects) (method : JsonRpc.Method) (params : Array Json) : IO Json := do
  if method != .chainId && method != .blockNumber && method != .call &&
      method != .getLogs && method != .gasPrice then fail
  let value ← try effects.rpc method params catch _ => fail
  if value.compress.toUTF8.size > maxRpcBytes then fail
  return value

private def callParams (target : Nat) (data : ByteArray) (block : Nat) : Array Json :=
  #[Json.mkObj [("to", toJson (addressText target)), ("data", toJson (hexText data))],
    toJson (quantity block)]

private def callWord (effects : Effects) (target : Nat) (data : ByteArray) (block : Nat) : IO Nat := do
  let value ← rpc effects .call (callParams target data block)
  return wordNat (← checked <| bytes (← checked value.getStr?) 32)

private def chainHead (effects : Effects) (chainId : Nat) : IO Nat := do
  let chain ← checked <| JsonRpc.parseHexQuantity (← checked (← rpc effects .chainId #[]).getStr?)
  if chain != chainId then fail
  let head ← checked <| JsonRpc.parseHexQuantity (← checked (← rpc effects .blockNumber #[]).getStr?)
  if head >= 2 ^ 64 then fail
  return head

def lookupWith (effects : Effects) (pool : Pool) (event : RegistryEvent) (block : Nat) : IO Registration := do
  let cfg ← checked <| config (chainNumber pool.chainId)
  let data ← checked <| aggregatorCall (← checked <| namehash event.ensName) cfg.subdomains
  let result ← rpc effects .call (callParams cfg.aggregator data block)
  let raw ← checked result.getStr?
  if raw.length > 32770 then fail
  checked <| decodeRegistration (← checked <| parseHexBytes raw)

private def registryRange (effects : Effects) (cfg : Config)
    (first last fuel : Nat) (requests : IO.Ref Nat) : IO (Array RegistryEvent) := do
  let count ← requests.get
  if count >= 4096 then fail
  requests.set (count + 1)
  let result? ← try some <$> rpc effects .getLogs #[Json.mkObj [
      ("address", toJson (addressText cfg.registry)),
      ("fromBlock", toJson (quantity first)), ("toBlock", toJson (quantity last)),
      ("topics", toJson #[hexText registryTopic])]]
    catch _ => pure none
  if let some result := result? then
    let entries ← checked result.getArr?
    if entries.size > maxRegistryEvents then fail
    entries.mapM fun value => checked <| decodeRegistryEvent cfg first last value
  else
    if first >= last then fail
    match fuel with
    | 0 => fail
    | fuel' + 1 =>
      let middle := first + (last - first) / 2
      let left ← registryRange effects cfg first middle fuel' requests
      let right ← registryRange effects cfg (middle + 1) last fuel' requests
      if left.size + right.size > maxRegistryEvents then fail
      return left ++ right
termination_by fuel

def discoverWith (effects : Effects) (pool : Pool) (head : Nat) : IO (Array (RegistryEvent × Registration)) := do
  if !canonicalClassicPool pool then fail
  let cfg ← checked <| config (chainNumber pool.chainId)
  if head < cfg.registryDeployment || head - cfg.registryDeployment > 30000000 then fail
  let requests ← IO.mkRef 0
  let started ← effects.nowMs
  let mut first := cfg.registryDeployment
  let mut events : Array RegistryEvent := #[]
  while first <= head do
    let now ← effects.nowMs
    if now < started || now - started > 300000 then fail
    let last := min head (first + 49999)
    let rows ← registryRange effects cfg first last 16 requests
    if events.size + rows.size > maxRegistryEvents then fail
    events := events ++ rows
    first := last + 1
  let mut unique : Array RegistryEvent := #[]
  for event in events do
    if let some existing := unique.findIdx? (fun prior => prior.ensName == event.ensName) then
      let old := unique[existing]!
      if event.block > old.block || (event.block == old.block && event.logIndex > old.logIndex) then
        unique := unique.set! existing event
    else unique := unique.push event
  if unique.size > maxRegistryCandidates then fail
  let mut registered := #[]
  for event in unique do
    let value? ← try some <$> lookupWith effects pool event head catch _ => pure none
    if let some value := value? then
      if value.registered && value.stake >= minStake && value.owner == event.owner &&
          value.records.size == 20 && !value.records[0]!.isEmpty then
        registered := registered.push (event, value)
  return registered

private def oracleReference (effects : Effects) (pool : Pool) (networkWei head : Nat) : IO (Option Nat) := do
  match pool.asset.token with
  | none => return none
  | some token =>
    let paymaster ← checked <| SponsoredWithdrawal.paymaster (chainNumber pool.chainId)
    let token ← checked <| address token
    let data := Abi.selector "quoteWeiInToken(address,uint256)" ++
      (← checked <| word token) ++ (← checked <| word networkWei)
    return some (← callWord effects paymaster data head)

structure Quote where
  private mk ::
  pool : Pool
  relayer : Relayer
  amounts : Amounts
  registrationEvent : RegistryEvent
  quotedAt : Nat
  fromBlock : Nat

/-- Read-only fee preparation. It cannot generate or transmit a proof. -/
def prepareWith (effects : Effects) (pool : Pool) : IO Quote := do
  let effects ← boundedEffects effects
  if !canonicalClassicPool pool then fail
  let head ← chainHead effects (chainNumber pool.chainId)
  let gasPrice ← checked <| JsonRpc.parseHexQuantity (← checked (← rpc effects .gasPrice #[]).getStr?)
  if gasPrice == 0 || gasPrice > maxGasPrice then fail
  let reference ← oracleReference effects pool (gasPrice * withdrawGas) head
  let candidates ← discoverWith effects pool head
  let mut best : Option (RegistryEvent × Relayer × Amounts) := none
  for (event, registered) in candidates.extract 0 maxRelayerChecks do
    let checked? ← try
        let cfg ← checked <| config (chainNumber pool.chainId)
        let url ← checked <| relayerUrl ("https://" ++ registered.records[cfg.subdomains.size - 1]! ++ "/")
        let raw ← effects.get (url ++ "status")
        let relayer ← checked <| checkStatus pool event registered raw
        let amounts ← checked <| quoteAmounts pool relayer gasPrice reference
        pure (some (event, relayer, amounts))
      catch _ => pure none
    if let some candidate := checked? then
      match best with
      | none => best := some candidate
      | some old => if candidate.2.2.fee < old.2.2.fee then best := some candidate
  let some (event, relayer, amounts) := best | fail
  if (← chainHead effects (chainNumber pool.chainId)) < head then fail
  return ⟨pool, relayer, amounts, event, ← effects.nowMs, head⟩

/-- Recheck registration, endpoint and service fee at a fresh provider block.
    A successful result still does not authorize or execute a withdrawal. -/
def recheckWith (effects : Effects) (quote : Quote) : IO Unit := do
  let effects ← boundedEffects effects
  let now ← effects.nowMs
  if now < quote.quotedAt || now - quote.quotedAt >= quoteLifetimeMs then fail
  let head ← chainHead effects (chainNumber quote.pool.chainId)
  if head < quote.fromBlock then fail
  let registration ← lookupWith effects quote.pool quote.registrationEvent head
  let raw ← try effects.get (quote.relayer.url ++ "status") catch _ => fail
  let current ← checked <| checkStatus quote.pool quote.registrationEvent registration raw
  if current.url != quote.relayer.url || current.rewardAccount != quote.relayer.rewardAccount ||
      current.serviceFeeBps != quote.relayer.serviceFeeBps then fail
  if (← chainHead effects (chainNumber quote.pool.chainId)) < head then fail
  let now ← effects.nowMs
  if now < quote.quotedAt || now - quote.quotedAt >= quoteLifetimeMs then fail

/-- Check a locally supplied proof against all reviewed public inputs and
    the selected registered reward account and fee. This only validates a
    public result; it cannot submit or generate a proof. -/
def validateProof (quote : Quote) (review : ProverWorkerWire.Request)
    (result : ProverWorkerWire.Result) : Except String (ProverWorkerClient.Accepted review) := do
  if !canonicalClassicPool quote.pool ||
      review.chainId != chainNumber quote.pool.chainId ||
      review.pool != (← address quote.pool.address) ||
      review.relayer != quote.relayer.rewardAccount ||
      review.fee != quote.amounts.fee || review.refund != 0 then throw invalid
  let some amounts := Tornado.Policy.validateRelayerFee
    ⟨quote.pool.amount, review.fee, quote.relayer.serviceFeeBps⟩ | throw invalid
  if quote.amounts != ⟨amounts.fee, amounts.net, amounts.serviceFee, amounts.networkFee⟩ then throw invalid
  ProverWorkerClient.acceptResponse review result

def nativeEffects (rpcUrl : String) : IO Effects := do
  if !HttpTransport.validRpcUrl rpcUrl then fail
  let nextId ← IO.mkRef (1 : Nat)
  return {
    rpc := fun method params => do
      if method != .chainId && method != .blockNumber && method != .call &&
          method != .getLogs && method != .gasPrice && method != .getTransactionReceipt then fail
      let id ← nextId.get
      if id > 8192 then fail
      nextId.set (id + 1)
      HttpTransport.call rpcUrl id method params,
    get := fun url => HttpTransport.getHttps url maxStatusBytes.toUInt32 true,
    nowMs := IO.monoMsNow }

structure Prepared where
  private mk ::
  quote : Quote
  request : ProverWorkerWire.Request
  accepted : ProverWorkerClient.Accepted request
  body : ByteArray

private def proofArgs (request : ProverWorkerWire.Request) : Except String (Array String) := do
  return #[hexText (← word request.root), hexText (← word request.nullifierHash),
    addressText request.recipient, addressText request.relayer,
    quantity request.fee, quantity request.refund]

/-- Construct the exact endpoint body only after native proof verification
    and all six reviewed public inputs agree with the registered quote. -/
def prepareProof (quote : Quote) (request : ProverWorkerWire.Request)
    (result : ProverWorkerWire.Result) : Except String Prepared := do
  let accepted ← validateProof quote request result
  let body := (Json.mkObj [
    ("proof", toJson (hexText accepted.proofBytes)),
    ("args", toJson (← proofArgs request)),
    ("contract", toJson (addressText request.pool))]).compress.toUTF8
  return ⟨quote, request, accepted, body⟩

/-- Native proof construction may take longer than the final review window.
    Refresh public policy after it finishes, while keeping the proof-bound
    reward, fee and exact executable bytes unchanged. Any current fee or
    relayer change requires a new preparation before anything is exposed. -/
def refreshPreparedWith (source : Effects) (prepared : Prepared) : IO Prepared := do
  let effects ← boundedEffects source
  let old := prepared.quote
  if (← effects.nowMs) < old.quotedAt then fail
  let head ← chainHead effects (chainNumber old.pool.chainId)
  if head < old.fromBlock then fail
  let registration ← lookupWith effects old.pool old.registrationEvent head
  let raw ← try effects.get (old.relayer.url ++ "status") catch _ => fail
  let current ← checked <| checkStatus old.pool old.registrationEvent registration raw
  if current.url != old.relayer.url || current.rewardAccount != old.relayer.rewardAccount ||
      current.serviceFeeBps != old.relayer.serviceFeeBps then fail
  let gasPrice ← checked <| JsonRpc.parseHexQuantity
    (← checked (← rpc effects .gasPrice #[]).getStr?)
  let reference ← oracleReference effects old.pool (gasPrice * withdrawGas) head
  let amounts ← checked <| quoteAmounts old.pool current gasPrice reference
  if amounts != old.amounts then fail
  if (← chainHead effects (chainNumber old.pool.chainId)) < head then fail
  let now ← effects.nowMs
  if now < old.quotedAt then fail
  let quote : Quote := ⟨old.pool, current, amounts, old.registrationEvent, now, head⟩
  return ⟨quote, prepared.request, prepared.accepted, prepared.body⟩

def statusRecord (prepared : Prepared) (rpcUrl : String) : Except String Json := do
  if !HttpTransport.validRpcUrl rpcUrl then throw invalid
  let request := prepared.request
  let root := Json.mkObj [
    ("version", toJson (1 : Nat)), ("kind", toJson ("relayer" : String)),
    ("chainId", toJson request.chainId),
    ("poolAddress", toJson (addressText request.pool)),
    ("nullifierHash", toJson (hexText (← word request.nullifierHash))),
    ("recipient", toJson (addressText request.recipient)),
    ("relayerUrl", toJson prepared.quote.relayer.url),
    ("rewardAccount", toJson (addressText request.relayer)),
    ("fee", toJson (quantity request.fee)),
    ("fromBlock", toJson (quantity prepared.quote.fromBlock)),
    ("rpcUrl", toJson rpcUrl), ("status", toJson ("unknown" : String)),
    ("message", toJson ("An executable relayer proof POST is reserved. Check this original attempt before retrying." : String)),
    ("nativeProofHash", toJson (hexText (keccak256 prepared.accepted.proofBytes))),
    ("nativeCalldataHash", toJson (hexText (keccak256 prepared.accepted.calldata))),
    ("nativeRequestHash", toJson (hexText request.hash)),
    ("nativePostBodyHash", toJson (hexText (keccak256 prepared.body))),
    ("nativeProofArgs", toJson (← proofArgs request))]
  let _ ← RelayerWithdrawalStatus.parseRecord root
  return root

def reviewText (prepared : Prepared) : String :=
  let quote := prepared.quote
  String.intercalate "\n" [
    s!"Chain: {prepared.request.chainId}",
    s!"Pool: {quote.pool.denomination} {quote.pool.asset.symbol} ({quote.pool.address})",
    s!"Recipient: {addressText prepared.request.recipient}",
    s!"Relayer: {quote.relayer.ensName} ({quote.relayer.url})",
    s!"Registered reward account: {addressText quote.relayer.rewardAccount}",
    s!"Total fee: {formatUnitsExact quote.amounts.fee quote.pool.asset.decimals} {quote.pool.asset.symbol}",
    s!"Service fee: {formatUnitsExact quote.amounts.serviceFee quote.pool.asset.decimals}; network fee: {formatUnitsExact quote.amounts.networkFee quote.pool.asset.decimals}",
    s!"Net withdrawal: {formatUnitsExact quote.amounts.net quote.pool.asset.decimals} {quote.pool.asset.symbol}",
    "No post-withdrawal contract calls."]

structure SubmissionEffects where
  readonly : Effects
  approve : String → IO Unit
  revalidate : ProverWorkerWire.Request → IO Unit
  reserve : String → IO Unit
  update : String → IO Unit
  post : String → ByteArray → IO ByteArray
  sleepMs : Nat → IO Unit

structure SubmissionOptions where
  waitMs : Nat := 180000
  pollMs : Nat := 2000
  deriving Inhabited

structure SubmissionResult where
  record : String
  output : String
  code : UInt32
  jobId : Option String
  journalUpdated : Bool
  deriving Inhabited

private def parseJobId (reply : ByteArray) : Except String String := do
  if reply.size > 8192 then throw invalid
  let some raw := String.fromUTF8? reply | throw invalid
  let json ← Json.parse raw
  let id ← text json "id"
  if id.isEmpty || id.length > 256 || !id.toList.all
      (fun c => asciiAlphaNum c.toLower || c == '_' || c == '-') then throw invalid
  return id

/-- Exactly one proof-bearing POST follows typed approval, current pool and
    relayer checks, and a durable exclusive claim. No transport error, lost
    job ID, job-only claim, or failed journal update permits another POST. -/
def submitWith (effects : SubmissionEffects) (prepared : Prepared) (rpcUrl : String)
    (options : SubmissionOptions := {}) : IO SubmissionResult := do
  if options.waitMs > 300000 || options.pollMs < 100 || options.pollMs > 10000 then fail
  let initial ← checked <| statusRecord prepared rpcUrl
  effects.approve (reviewText prepared)
  recheckWith effects.readonly prepared.quote
  effects.revalidate prepared.request
  let now ← effects.readonly.nowMs
  if now < prepared.quote.quotedAt || now - prepared.quote.quotedAt >= quoteLifetimeMs then fail
  let initialRaw := initial.compress ++ "\n"
  -- This reservation includes exact args and hashes of proof/call/body, but
  -- never stores the executable proof itself or the note's secret preimage.
  effects.reserve initialRaw
  let reply? ← try
      some <$> effects.post (prepared.quote.relayer.url ++ "v1/tornadoWithdraw") prepared.body
    catch _ => pure none
  let jobId := reply?.bind (fun reply => (parseJobId reply).toOption)
  let pending := match jobId with
    | none => initial.setObjVal! "message" (toJson
        ("Relayer submission outcome is unknown. Do not repeat the POST; reconcile the original attempt from chain evidence." : String))
    | some id => (initial.setObjVal! "jobId" (toJson id)).setObjVal! "status" (toJson ("pending" : String))
  let mut raw := pending.compress ++ "\n"
  let mut journalUpdated := true
  try effects.update raw catch _ => journalUpdated := false
  let started ← effects.readonly.nowMs
  let limit := min 128 (options.waitMs / options.pollMs + 1)
  let mut output := "Status: unknown\nThe proof POST may have reached the relayer; reconcile the original attempt before further action.\n"
  let mut code : UInt32 := 2
  for index in [0:limit] do
    let reconciled? ← try some <$> RelayerWithdrawalStatus.reconcileWith raw effects.readonly.rpc
      catch _ => pure none
    if let some (next, summary, resultCode) := reconciled? then
      raw := next
      output := summary
      code := resultCode
      try effects.update raw catch _ => journalUpdated := false
    if code == 0 then break
    let now ← effects.readonly.nowMs
    if now < started || now - started >= options.waitMs || index + 1 >= limit then break
    effects.sleepMs (min options.pollMs (options.waitMs - (now - started)))
  if !journalUpdated then
    output := output ++ "The protected status journal could not be fully updated. Its original reservation remains; keep this attempt and reconcile it before any replacement.\n"
    code := 2
  return ⟨raw, output, code, jobId, journalUpdated⟩

structure Journal where
  reserve : String → IO Unit
  update : String → IO Unit

private def withoutField (json : Json) (name : String) : Json :=
  match json with
  | .obj entries => .obj (entries.erase name)
  | other => other

private def reservedIdentity (json : Json) : Except String Json := do
  let _ ← RelayerWithdrawalStatus.parseRecord json
  return ["status", "message", "jobId", "transactionHash"].foldl withoutField json

/-- A new opaque per-note path is the permanent exclusive claim shared with
    the 4337 routes. Known job/transaction identifiers cannot be replaced.
    Stale or raced updates fail the protected byte-for-byte CAS. -/
def protectedJournal (path : String) : IO Journal := do
  if !(System.FilePath.mk path).isAbsolute then fail
  let saved ← IO.mkRef (none : Option ByteArray)
  return {
    reserve := fun raw => do
      if (← saved.get).isSome || raw.utf8ByteSize > 65536 then fail
      let root ← checked <| Json.parse raw
      let _ ← checked <| reservedIdentity root
      let record ← checked <| RelayerWithdrawalStatus.parseRecord root
      let namePrefix := s!"tornado-withdraw-{chainNumber record.chainId}-"
      let name := ((System.FilePath.mk path).fileName).getD ""
      let digest := (name.toList.drop namePrefix.length).take 64
      if !name.startsWith namePrefix || !name.endsWith ".json" ||
          name.length != namePrefix.length + 69 ||
          !digest.all (fun c => ('0' <= c && c <= '9') || ('a' <= c && c <= 'f')) then fail
      WithdrawalJournalProgram.createProtected path raw.toUTF8
      saved.set (some raw.toUTF8),
    update := fun raw => do
      let some old ← saved.get | fail
      if raw.utf8ByteSize > 65536 then fail
      let some oldText := String.fromUTF8? old | fail
      let prior ← checked <| Json.parse oldText
      let mut next ← checked <| Json.parse raw
      if (← checked <| reservedIdentity prior) != (← checked <| reservedIdentity next) then fail
      for name in ["jobId", "transactionHash"] do
        if let .ok value := field prior name then
          match field next name with
          | .error _ => next := next.setObjVal! name value
          | .ok current => if current != value then fail
      let updated := (next.compress ++ "\n").toUTF8
      WithdrawalJournalProgram.replaceProtected path old updated
      saved.set (some updated) }

end Tornado.Cli.RelayerSend
