import Tornado.Domain.ChainInput
import Tornado.Domain.NoteIdentity
import Tornado.SmartAccount.Recovery
import Tornado.SmartAccount.Address
import Tornado.Runtime.HttpTransport

/-!
Read-only inspection of the UI-compatible SimpleAccount. Every chain value
comes from the selected RPC; the pinned code and deployed-account checks
detect mismatches in that RPC's answers, not dishonest chain data. No key,
signature, proof, or transaction is read or sent.
-/

namespace Tornado.Cli.SmartAccountShow

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol
open Tornado.SmartAccount Tornado.Runtime

/-- Both supported chains use the v0.8 EntryPoint in the pinned SDK catalog. -/
def entryPoint : String := "0x4337084D9E255Ff0702461CF8895CE9E3b5Ff108"

private def fromExcept (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def natFromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def lowerAddress (address : Nat) : Except String String := do
  if address == 0 || address >= Abi.maxAddress then
    throw "Ethereum address must be nonzero and 20 bytes."
  let word ← Abi.addressWord address
  return "0x" ++ bytesToHex (word.extract 12 32)

/-- EIP-55 address text. Mixed-case input is checked against this spelling. -/
def checksumAddress (address : Nat) : Except String String := do
  let lower ← lowerAddress address
  let digits := (String.ofList (lower.toList.drop 2)).toList.toArray
  let hash := keccak256 (String.ofList digits.toList).toUTF8
  let mut output := "0x"
  for i in [0:digits.size] do
    let letter := digits[i]!
    let byte := hash[i / 2]!.toNat
    let nibble := if i % 2 == 0 then byte / 16 else byte % 16
    output := output.push (if nibble >= 8 then letter.toUpper else letter)
  return output

/-- Viem-compatible nonzero address acceptance, including EIP-55 on mixed
    case text. It does not query whether the address is an EOA. -/
def parseOwner (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" || raw.length != 42 then
    throw "Owner must be a nonzero Ethereum address."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Owner must be a nonzero Ethereum address."
  let owner := natFromBytes bytes
  if owner == 0 then throw "Owner must be a nonzero Ethereum address."
  let payload := String.ofList (raw.toList.drop 2)
  if payload != payload.toLower && payload != payload.toUpper &&
      raw != (← checksumAddress owner) then
    throw "Owner must be a nonzero Ethereum address."
  return owner

private def parseAddressWord (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" then throw "RPC ABI address has no 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "RPC ABI address must be one word."
  if !(bytes.extract 0 12).data.all (· == 0) then
    throw "RPC ABI address has nonzero high bytes."
  let address := natFromBytes (bytes.extract 12 32)
  if address == 0 then throw "RPC ABI address is zero."
  return address

/-- Strict ABI address result for eth_call. -/
def decodeAddressResult (value : Json) : Except String Nat :=
  parseAddressWord value

/-- Strict uint256 ABI result for eth_call. -/
def decodeUintResult (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" then throw "RPC ABI uint256 has no 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "RPC ABI uint256 must be one word."
  return natFromBytes bytes

/-- Code and storage responses are fixed-format Ethereum data, not quantities. -/
def decodeCodeResult (value : Json) : Except String ByteArray := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" then throw "RPC code has no 0x prefix."
  parseHexBytes raw

def decodeSlotResult (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" then throw "RPC storage has no 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "RPC storage must be one word."
  return natFromBytes bytes

def decodeQuantityResult (value : Json) : Except String Nat := do
  JsonRpc.parseHexQuantity (← value.getStr?)

private def rpcData (bytes : ByteArray) : Json :=
  toJson ("0x" ++ bytesToHex bytes)

/-- Factory getAddress calldata shares the exact salt and ABI builder used
    by the pure recovery module. -/
def getAddressData (owner : Nat) : Except String ByteArray := do
  let _ ← accountFactoryData owner
  return Abi.selector "getAddress(address,uint256)" ++
    (← Abi.addressWord owner) ++ (← Abi.uintWord withdrawalAccountSalt)

private def ownerData (account : Nat) : Except String ByteArray :=
  Abi.addressWord account

def callParams (target : String) (data : ByteArray) (block : String) : Array Json :=
  #[Json.mkObj [("to", toJson target), ("data", rpcData data)], toJson block]

def codeParams (address block : String) : Array Json :=
  #[toJson address, toJson block]

def balanceParams (address block : String) : Array Json :=
  #[toJson address, toJson block]

def slotParams (address block : String) : Array Json :=
  #[toJson address, toJson implementationSlot, toJson block]

private def plainAddress (raw : String) : Except String Nat := do
  let bytes ← parseHexBytes raw
  if !raw.startsWith "0x" || bytes.size != 20 then
    throw "Pinned contract address is invalid."
  return natFromBytes bytes

structure IdentityReadings where
  owner : Nat
  factoryCode : ByteArray
  ownerCode : ByteArray
  implementation : Nat
  implementationCode : ByteArray
  implementationEntryPoint : Nat
  account : Nat
  accountCode : ByteArray
  nonce : Nat
  actualOwner : Option Nat := none
  actualEntryPoint : Option Nat := none
  slotValue : Option Nat := none
  deriving Inhabited

structure Account where
  owner : Nat
  address : Nat
  deployed : Bool
  nonce : Nat
  deriving Inhabited, BEq

/-- Pure validation of all identity readings before any balance is displayed. -/
def validateIdentity (readings : IdentityReadings) : Except String Account := do
  if readings.owner == 0 || readings.owner >= Abi.maxAddress ||
      readings.account == 0 || readings.account >= Abi.maxAddress ||
      readings.implementation == 0 || readings.implementation >= Abi.maxAddress then
    throw "Smart-account identity includes an invalid address."
  if !pinnedFactoryCode readings.factoryCode then
    throw "The pinned SimpleAccount v0.8 factory is unavailable."
  if !ownerCodeAllowed readings.ownerCode then
    throw "Contract-wallet owners are not supported for this smart account."
  let expectedEntryPoint ← plainAddress entryPoint
  if !pinnedImplementationCode readings.implementationCode ||
      readings.implementationEntryPoint != expectedEntryPoint then
    throw "The SimpleAccount implementation or EntryPoint does not match v0.8."
  Tornado.SmartAccount.Address.validateReported readings.owner
    readings.implementation readings.account
  let deployed := !readings.accountCode.isEmpty
  if deployed then
    let some actualOwner := readings.actualOwner
      | throw "Deployed smart-account owner is missing."
    let some actualEntryPoint := readings.actualEntryPoint
      | throw "Deployed smart-account EntryPoint is missing."
    let some slotValue := readings.slotValue
      | throw "Deployed smart-account implementation slot is missing."
    if !deployedAccountIdentityValid readings.owner expectedEntryPoint
        readings.implementation actualOwner actualEntryPoint slotValue then
      throw "The deployed smart account has a different owner, implementation or EntryPoint."
  return ⟨readings.owner, readings.account, deployed, readings.nonce⟩

structure BalanceRow where
  asset : Asset
  amount : Nat
  deriving Inhabited, BEq

/-- Pure catalog-order output matching the pinned TypeScript show command. -/
def render (chain : ChainId) (account : Account) (balances : Array BalanceRow)
    (entryPointDeposit : Nat) : Except String String := do
  if balances.toList.map (·.asset) != assetsFor chain then
    throw "Smart-account balances do not match the supported asset catalog."
  let owner ← checksumAddress account.owner
  let smartAccount ← checksumAddress account.address
  let mut lines := [
    s!"Owner: {owner}",
    s!"Smart account: {smartAccount}",
    s!"Deployed: {if account.deployed then "yes" else "no"}",
    s!"EntryPoint nonce: {account.nonce}"]
  for row in balances do
    if row.amount >= Abi.maxUint256 then throw "Balance is outside uint256."
    lines := lines ++ [s!"{row.asset.symbol}: {formatUnitsExact row.amount row.asset.decimals}"]
  if entryPointDeposit >= Abi.maxUint256 then
    throw "EntryPoint deposit is outside uint256."
  lines := lines ++ [s!"EntryPoint deposit: {formatUnitsExact entryPointDeposit 18} ETH"]
  return String.intercalate "\n" lines ++ "\n"

private structure Options where
  owner : Option String := none
  chain : String := "1"
  rpc : Option String := none
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--owner" :: value :: rest => parseOptions rest { options with owner := some value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | ["--owner"] => .error "error: option '--owner <address>' argument missing"
  | ["--chain"] => .error "error: option '--chain <id>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--owner=" then
        parseOptions rest { options with owner := some (String.ofList (item.toList.drop 8)) }
      else if item.startsWith "--chain=" then
        parseOptions rest { options with chain := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else if item.startsWith "-" then .error s!"error: unknown option '{item}'"
      else .error "error: too many arguments"

private def showHelp : String :=
  "Usage: tornado smart-account show [options]\n\n" ++
  "Show the deterministic smart account and its supported balances\n\n" ++
  "Options:\n" ++
  "  --owner <address>  EOA that controls the smart account\n" ++
  "  --chain <id>      Ethereum chain ID (default: \"1\")\n" ++
  "  --rpc <url>       Chain RPC URL\n" ++
  "  -h, --help        display help for command\n"

/-- Command entry point. The only effectful operation is typed JSON-RPC over
    the pinned HTTPS transport. All mutable state stays inside the command. -/
def showCommand (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.showHelp then return showHelp
  let some ownerRaw := options.owner
    | throw <| IO.userError "error: required option '--owner <address>' not specified"
  let owner ← fromExcept (parseOwner ownerRaw)
  let ownerText ← fromExcept (checksumAddress owner)
  let chain ← fromExcept (parseChainInput options.chain)
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let requestId ← IO.mkRef (1 : Nat)
  let read (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params
  let actualChain ← fromExcept <| decodeQuantityResult (← read .chainId #[])
  if actualChain != chainNumber chain then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let blockValue ← read .blockNumber #[]
  let block ← fromExcept blockValue.getStr?
  let _ ← fromExcept (JsonRpc.parseHexQuantity block)
  let factoryCode ← fromExcept <| decodeCodeResult
    (← read .getCode (codeParams simpleAccountFactory block))
  if !pinnedFactoryCode factoryCode then
    throw <| IO.userError "The pinned SimpleAccount v0.8 factory is unavailable."
  let ownerCode ← fromExcept <| decodeCodeResult
    (← read .getCode (codeParams ownerText block))
  if !ownerCodeAllowed ownerCode then
    throw <| IO.userError "Contract-wallet owners are not supported for this smart account."
  let implementation ← fromExcept <| decodeAddressResult
    (← read .call (callParams simpleAccountFactory
      (Abi.selector "accountImplementation()") block))
  let accountAddress ← fromExcept <| decodeAddressResult
    (← read .call (callParams simpleAccountFactory
      (← fromExcept (getAddressData owner)) block))
  let implementationText ← fromExcept (checksumAddress implementation)
  let accountText ← fromExcept (checksumAddress accountAddress)
  let implementationCode ← fromExcept <| decodeCodeResult
    (← read .getCode (codeParams implementationText block))
  let implementationEntryPoint ← fromExcept <| decodeAddressResult
    (← read .call (callParams implementationText
      (Abi.selector "entryPoint()") block))
  let accountCode ← fromExcept <| decodeCodeResult
    (← read .getCode (codeParams accountText block))
  let entryPointNonce ← fromExcept <| decodeUintResult
    (← read .call (callParams entryPoint
      (Abi.selector "getNonce(address,uint192)" ++
        (← fromExcept (ownerData accountAddress)) ++
        (← fromExcept (Abi.uintWord 0))) block))
  let mut actualOwner : Option Nat := none
  let mut actualEntryPoint : Option Nat := none
  let mut slotValue : Option Nat := none
  if !accountCode.isEmpty then
    actualOwner := some (← fromExcept <| decodeAddressResult
      (← read .call (callParams accountText (Abi.selector "owner()") block)))
    actualEntryPoint := some (← fromExcept <| decodeAddressResult
      (← read .call (callParams accountText (Abi.selector "entryPoint()") block)))
    slotValue := some (← fromExcept <| decodeSlotResult
      (← read .getStorageAt (slotParams accountText block)))
  let account ← fromExcept <| validateIdentity {
    owner := owner, factoryCode := factoryCode, ownerCode := ownerCode,
    implementation := implementation, implementationCode := implementationCode,
    implementationEntryPoint := implementationEntryPoint,
    account := accountAddress, accountCode := accountCode,
    nonce := entryPointNonce, actualOwner := actualOwner,
    actualEntryPoint := actualEntryPoint, slotValue := slotValue }
  let mut balances := #[]
  for asset in assetsFor chain do
    let amount ← match asset.token with
      | none => do
          fromExcept <| decodeQuantityResult
            (← read .getBalance (balanceParams accountText block))
      | some token => do
          fromExcept <| decodeUintResult
            (← read .call (callParams token
              (Abi.selector "balanceOf(address)" ++
                (← fromExcept (ownerData accountAddress))) block))
    balances := balances.push { asset, amount }
  let deposit ← fromExcept <| decodeUintResult
    (← read .call (callParams entryPoint
      (Abi.selector "balanceOf(address)" ++
        (← fromExcept (ownerData accountAddress))) block))
  fromExcept (render chain account balances deposit)

end Tornado.Cli.SmartAccountShow
