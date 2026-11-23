import Tornado.Cli.RelayerSend

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Cli.RelayerSend

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message
private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message
private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try let _ ← action; pure false catch _ => pure true
  require failed message
private def jsonField (json : Json) (key : String) : IO Json := checked <| json.getObjVal? key
private def jsonString (json : Json) (key : String) : IO String := do
  checked (← jsonField json key).getStr?
private def fieldBytes (json : Json) (key : String) : IO ByteArray := do
  checked <| parseHexBytes (← jsonString json key)
private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

private def mockEffects (fixture : Json) (wrongChain : Bool := false)
    (stakeTooSmall : Bool := false) (changedStatus : Bool := false)
    (clock : Nat := 0) : IO (Effects × IO.Ref Nat × IO.Ref Nat) := do
  let cfg ← checked <| config 1
  let registryEvent ← jsonField fixture "registryEvent"
  let response ← fieldBytes fixture "aggregatorResponse"
  let response := if stakeTooSmall then
      (response.extract 0 128) ++ word (minStake - 1) ++ response.extract 160 response.size
    else response
  let status ← jsonField fixture "status"
  let status := if changedStatus then status.setObjVal! "rewardAccount"
    (toJson ("0x00000000000000000000000000000000000000cc" : String)) else status
  let statusCalls ← IO.mkRef 0
  let rangeCalls ← IO.mkRef 0
  let expectedCall ← jsonString fixture "aggregatorCall"
  let effects : Effects := {
    nowMs := pure clock,
    get := fun url => do
      require (url == "https://relayer.example.org/status") "Unexpected relayer GET URL"
      statusCalls.modify (· + 1)
      return status.compress.toUTF8,
    rpc := fun method params => do
      match method with
      | .chainId => return toJson (if wrongChain then "0xaa36a7" else "0x1")
      | .blockNumber => return toJson ("0x" ++ String.ofList (Nat.toDigits 16 (cfg.registryDeployment + 4)))
      | .gasPrice => return toJson ("0x3b9aca00" : String)
      | .getLogs =>
        rangeCalls.modify (· + 1)
        let first ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| params[0]!.getObjVal? "fromBlock").getStr?)
        let last ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| params[0]!.getObjVal? "toBlock").getStr?)
        if last - first + 1 > 2 then throw <| IO.userError "RPC range limit"
        return Json.arr (if first <= cfg.registryDeployment && cfg.registryDeployment <= last
          then #[registryEvent] else #[])
      | .call =>
        let data ← checked <| (← checked <| params[0]!.getObjVal? "data").getStr?
        require (data == expectedCall) "Relayer aggregator calldata differs from viem"
        return toJson ("0x" ++ bytesToHex response)
      | _ => throw <| IO.userError "Read-only relayer workflow requested a forbidden RPC method" }
  return (effects, statusCalls, rangeCalls)

def main : IO UInt32 := do
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/classic-relayer.json")
  let cfg ← checked <| config 1
  let node ← checked <| namehash "example.eth"
  require (node == (← fieldBytes fixture "namehash")) "Native ENS namehash differs from viem"
  require ((← checked <| namehash "EXAMPLE.ETH") == node) "ASCII ENS case normalization changed"
  require (!(namehash "éxample.eth").isOk && !(namehash "bad..eth").isOk)
    "Unsupported ENS normalization was accepted"
  require ((← checked <| aggregatorCall node cfg.subdomains) ==
    (← fieldBytes fixture "aggregatorCall")) "Single-subdomain aggregator calldata differs from viem"
  let sepolia ← checked <| config 11155111
  require ((← checked <| aggregatorCall node sepolia.subdomains) ==
    (← fieldBytes fixture "aggregatorCallSepolia")) "Two-subdomain aggregator calldata differs from viem"
  let encoded ← fieldBytes fixture "aggregatorResponse"
  let registration ← checked <| decodeRegistration encoded
  require ((← checked <| encodeRegistration registration) == encoded &&
    registration.owner == 187 && registration.stake == minStake)
    "Canonical aggregator response differs from viem"
  require (!(decodeRegistration (encoded ++ word 0)).isOk)
    "Trailing aggregator ABI bytes were accepted"
  let invalidBool := encoded.extract 0 160 ++ word 2 ++ encoded.extract 192 encoded.size
  require (!(decodeRegistration invalidBool).isOk) "Noncanonical registration bool was accepted"
  let log ← jsonField fixture "registryEvent"
  let event ← checked <| decodeRegistryEvent cfg cfg.registryDeployment (cfg.registryDeployment + 4) log
  require (event.ensName == "example.eth" && event.owner == registration.owner)
    "Pinned registry event differs from viem"
  require (!(decodeRegistryEvent cfg cfg.registryDeployment (cfg.registryDeployment + 4)
    (log.setObjVal! "removed" (toJson true))).isOk) "Removed registry log was accepted"
  require (!(decodeRegistryEvent cfg cfg.registryDeployment (cfg.registryDeployment + 4)
    (log.setObjVal! "address" (toJson ("0x00000000000000000000000000000000000000bb" : String)))).isOk)
    "Wrong registry emitter was accepted"
  for url in ["http://relayer.example.org/", "https://user:pass@relayer.example.org/",
    "https://127.0.0.1/", "https://localhost/", "https://example.local/",
    "https://relayer.example.org/path", "https://relayer.example.org/?key=secret"] do
    require (!(relayerUrl url).isOk) "Unsafe relayer origin was accepted"
  let some pool := poolFor .mainnet "0.1" "ETH" | throw <| IO.userError "Missing original pool"
  let some extended := poolFor .mainnet "0.01" "ETH" | throw <| IO.userError "Missing extended pool"
  let status ← jsonField fixture "status"
  let relayer ← checked <| checkStatus pool event registration status.compress.toUTF8
  require (relayer.serviceFeeBps == 31 && relayer.url == "https://relayer.example.org/")
    "Relayer status fee or endpoint changed"
  require (!(checkStatus extended event registration status.compress.toUTF8).isOk)
    "Extended pool was accepted by Classic relayer"
  for forged in [{ pool with amount := pool.amount * 100 },
      { pool with asset := { pool.asset with decimals := 8 } },
      { pool with asset := { pool.asset with token := some "0x0000000000000000000000000000000000000001" } }] do
    require (!(checkStatus forged event registration status.compress.toUTF8).isOk)
      "Forged catalog amount or asset metadata was accepted"
    require (!(quoteAmounts forged relayer 1000000000 none).isOk)
      "A forged pool amount or asset affected the fee quote"
  for badStatus in [
    status.setObjVal! "currentQueue" (toJson (6 : Nat)),
    status.setObjVal! "tornadoServiceFee" (toJson (1 : Nat)),
    status.setObjVal! "tornadoServiceFee" (← checked <| Json.parse "0.001"),
    status.setObjVal! "netId" (toJson (11155111 : Nat)),
    status.setObjVal! "rewardAccount" (toJson ("0x00000000000000000000000000000000000000cc" : String))] do
    require (!(checkStatus pool event registration badStatus.compress.toUTF8).isOk)
      "An out-of-bounds status or reward mismatch was accepted"
  require (!(checkStatus pool event { registration with stake := minStake - 1 }
    status.compress.toUTF8).isOk) "Insufficient TORN stake was accepted"
  let amounts ← checked <| quoteAmounts pool relayer 1000000000 none
  require (amounts.networkFee == 550000000000000 && amounts.serviceFee == 310000000000000 &&
    amounts.fee == 860000000000000 && amounts.net + amounts.fee == pool.amount)
    "ETH network/service fee arithmetic changed"
  require (!(quoteAmounts pool relayer maxGasPrice none).isOk)
    "A total fee above 20 percent was accepted"
  let some tokenPool := poolFor .mainnet "100" "DAI" | throw <| IO.userError "Missing DAI pool"
  let tokenRelayer ← checked <| checkStatus tokenPool event registration status.compress.toUTF8
  let tokenAmounts ← checked <| quoteAmounts tokenPool tokenRelayer 1000000000 (some (10 ^ 18))
  require (tokenAmounts.networkFee == 1100000000000000000)
    "Token network fee conversion changed"
  require (!(quoteAmounts tokenPool tokenRelayer 1000000000 none).isOk)
    "Token quote without an independent oracle reference was accepted"
  require (!(quoteAmounts tokenPool { tokenRelayer with tokenPrice := some 100000000000000 }
    1000000000 (some (10 ^ 18))).isOk) "Adverse token oracle price deviation was accepted"
  let (effects, statusCalls, rangeCalls) ← mockEffects fixture
  rejects (prepareWith effects { pool with amount := pool.amount * 100 })
    "Discovery accepted a genuine pool address with forged note value"
  let quote ← prepareWith effects pool
  require (quote.amounts == amounts && (← statusCalls.get) == 1 && (← rangeCalls.get) > 1)
    "Read-only relayer discovery, range splitting or best quote failed"
  recheckWith effects quote
  let (wrongChain, _, _) ← mockEffects fixture true
  rejects (prepareWith wrongChain pool) "Wrong RPC network was accepted"
  let (lowStake, calls, _) ← mockEffects fixture false true
  rejects (prepareWith lowStake pool) "Relayer without 40 TORN stake was selected"
  require ((← calls.get) == 0) "Unregistered relayer status endpoint was contacted"
  let (changedReward, _, _) ← mockEffects fixture false false true
  rejects (recheckWith changedReward quote) "Changed reward account survived recheck"
  let (expired, _, _) ← mockEffects fixture false false false quoteLifetimeMs
  rejects (recheckWith expired quote) "Expired relayer quote survived recheck"
  IO.println "PASS: native relayer discovery, viem registry ABI, HTTPS status, stake, fee caps, oracle deviation and quote rechecks"
  return 0
