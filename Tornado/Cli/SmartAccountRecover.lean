import Lean
import Tornado.Cli.SmartAccountShow
import Tornado.Domain.ChainInput
import Tornado.SmartAccount.Recovery
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.NativeSigner

/-!
Read-only native recovery planning for the pinned SimpleAccount v0.8.
This command may derive the owner from a protected key through the native
signer boundary, but does not import private key bytes into Lean, sign, create
a journal, or send a transaction. Identity and balance reads use one RPC block.
-/

namespace Tornado.Cli.SmartAccountRecover

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.SmartAccount
open Tornado.Runtime Tornado.Cli.SmartAccountShow

private def fromExcept (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

structure Review where
  chainId : ChainId
  blockNumber : Nat
  account : SmartAccountShow.Account
  plan : RecoveryPlan
  deriving Inhabited

/-- Validate the pinned factory, implementation, deployed account identity,
    and all supported balances before constructing the pure recovery plan. -/
def inspectWith (chainId : ChainId) (owner recipient : Nat)
    (read : JsonRpc.Method → Array Json → IO Json) : IO Review := do
  let ownerText ← fromExcept (checksumAddress owner)
  let _ ← fromExcept (checksumAddress recipient)
  let actualChain ← fromExcept <| decodeQuantityResult (← read .chainId #[])
  if actualChain != chainNumber chainId then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let block ← fromExcept <| (← read .blockNumber #[]).getStr?
  let blockNumber ← fromExcept (JsonRpc.parseHexQuantity block)

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
  if accountCode.isEmpty then
    throw <| IO.userError "This smart account has not been deployed yet."
  let entryPointNonce ← fromExcept <| decodeUintResult
    (← read .call (callParams entryPoint
      (Abi.selector "getNonce(address,uint192)" ++
        (← fromExcept (Abi.addressWord accountAddress)) ++
        (← fromExcept (Abi.uintWord 0))) block))
  let actualOwner ← fromExcept <| decodeAddressResult
    (← read .call (callParams accountText (Abi.selector "owner()") block))
  let actualEntryPoint ← fromExcept <| decodeAddressResult
    (← read .call (callParams accountText (Abi.selector "entryPoint()") block))
  let slotValue ← fromExcept <| decodeSlotResult
    (← read .getStorageAt (slotParams accountText block))
  let account ← fromExcept <| validateIdentity {
    owner := owner, factoryCode := factoryCode, ownerCode := ownerCode,
    implementation := implementation, implementationCode := implementationCode,
    implementationEntryPoint := implementationEntryPoint,
    account := accountAddress, accountCode := accountCode,
    nonce := entryPointNonce, actualOwner := some actualOwner,
    actualEntryPoint := some actualEntryPoint, slotValue := some slotValue }
  if !account.deployed then
    throw <| IO.userError "This smart account has not been deployed yet."
  if recipient == account.address then
    throw <| IO.userError "Recovery recipient must differ from the smart account."

  let mut balances := #[]
  for asset in assetsFor chainId do
    let amount ← match asset.token with
      | none => do
          let result ← read .getBalance (balanceParams accountText block)
          fromExcept (decodeQuantityResult result)
      | some token => do
          let data := Abi.selector "balanceOf(address)" ++
            (← fromExcept (Abi.addressWord accountAddress))
          let result ← read .call (callParams token data block)
          fromExcept (decodeUintResult result)
    balances := balances.push amount
  let depositData := Abi.selector "balanceOf(address)" ++
    (← fromExcept (Abi.addressWord accountAddress))
  let entryPointDeposit ← fromExcept <| decodeUintResult
    (← read .call (callParams entryPoint depositData block))
  let plan ← fromExcept <| planRecovery chainId owner account.address recipient
    balances entryPointDeposit
  return ⟨chainId, blockNumber, account, plan⟩

/-- Public review output; call bytes are printed so another implementation can
    independently compare the proposed owner-paid transaction. -/
def render (review : Review) : Except String String := do
  if review.plan.owner != review.account.owner ||
      review.plan.account != review.account.address ||
      !review.account.deployed ||
      review.plan.balances.size != (assetsFor review.chainId).length ||
      !encodedCallsMatch review.plan.calls review.plan.data then
    throw "Recovery review does not match the checked account and calls."
  let owner ← checksumAddress review.plan.owner
  let account ← checksumAddress review.plan.account
  let receiver ← checksumAddress review.plan.recipient
  let mut lines := [s!"Owner: {owner}", s!"Smart account: {account}",
    s!"Receiver: {receiver}", s!"Block: {review.blockNumber}"]
  for (asset, amount) in (assetsFor review.chainId).zip review.plan.balances.toList do
    if amount > 0 then
      lines := lines ++ [s!"Recover {formatUnitsExact amount asset.decimals} {asset.symbol}"]
  if review.plan.entryPointDeposit > 0 then
    lines := lines ++ [s!"Recover {formatUnitsExact review.plan.entryPointDeposit 18} ETH EntryPoint deposit"]
  lines := lines ++ [s!"Calls: {review.plan.calls.size}"]
  for index in [0:review.plan.calls.size] do
    let call := review.plan.calls[index]!
    let target ← checksumAddress call.to
    lines := lines ++ [s!"Call {index + 1}: target={target} valueWei={call.value} data=0x{bytesToHex call.data}"]
  lines := lines ++ ["Account calldata: 0x" ++ bytesToHex review.plan.data,
    "Dry run complete. No recovery transaction was signed or submitted."]
  return String.intercalate "\n" lines ++ "\n"

private structure Options where
  owner : Option String := none
  ownerKeyFile : Option String := none
  passwords : NativeSigner.PasswordOptions := {}
  receiver : Option String := none
  chain : String := "1"
  rpc : Option String := none
  dryRun : Bool := false
  nonInteractive : Bool := false
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--dry-run" :: rest => parseOptions rest { options with dryRun := true }
  | "--non-interactive" :: rest => parseOptions rest { options with nonInteractive := true }
  | "--owner" :: value :: rest => parseOptions rest { options with owner := some value }
  | "--owner-key-file" :: value :: rest => parseOptions rest { options with ownerKeyFile := some value }
  | "--pwd" :: _ => .error "--pwd is not supported. Use --pwd-file or hidden password entry."
  | "--pwd-file" :: value :: rest => do
    let passwords ← options.passwords.withPasswordFile value
    parseOptions rest { options with passwords }
  | "--receiver" :: value :: rest => parseOptions rest { options with receiver := some value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | ["--owner"] => .error "error: option '--owner <address>' argument missing"
  | ["--owner-key-file"] => .error "error: option '--owner-key-file <path>' argument missing"
  | ["--pwd-file"] => .error "Password option is missing its value."
  | ["--receiver"] => .error "error: option '--receiver <address>' argument missing"
  | ["--chain"] => .error "error: option '--chain <id>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--pwd=" then
        .error "--pwd is not supported. Use --pwd-file or hidden password entry."
      else if item.startsWith "--pwd-file=" then do
        let passwords ← options.passwords.withPasswordFile (String.ofList (item.toList.drop 11))
        parseOptions rest { options with passwords }
      else if item.startsWith "--owner=" then
        parseOptions rest { options with owner := some (String.ofList (item.toList.drop 8)) }
      else if item.startsWith "--owner-key-file=" then
        parseOptions rest { options with ownerKeyFile := some (String.ofList (item.toList.drop 17)) }
      else if item.startsWith "--receiver=" then
        parseOptions rest { options with receiver := some (String.ofList (item.toList.drop 11)) }
      else if item.startsWith "--chain=" then
        parseOptions rest { options with chain := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else .error s!"error: unsupported recovery-planning option '{item}'"

private def help : String :=
  "Usage: tornado smart-account recover --owner <address> --dry-run [options]\n\n" ++
  "Review a supported-asset and EntryPoint-deposit recovery without signing.\n" ++
  "  --owner-key-file <path>  Derive owner through the protected native key boundary\n" ++
  "  --pwd-file <path>  Unlock an encrypted Web3 v3 owner key file\n" ++
  "  --receiver <address>  Recovery destination (default: owner)\n" ++
  "  --chain <id>         Ethereum chain ID (default: 1)\n" ++
  "  --rpc <url>          HTTPS chain RPC URL\n" ++
  "  --dry-run            Required; this native command cannot submit\n" ++
  "  --non-interactive    Require --owner or --owner-key-file; never prompt for a key\n"

def recoverCommand (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.help then return help
  if options.nonInteractive && options.owner.isNone && options.ownerKeyFile.isNone then
    throw <| IO.userError "--non-interactive requires --owner or --owner-key-file for recovery review."
  if !options.dryRun then
    throw <| IO.userError "Native smart-account recovery only supports --dry-run."
  if options.ownerKeyFile.isNone && options.passwords.hasSource then
    throw <| IO.userError "--pwd-file requires --owner-key-file."
  let chain ← fromExcept (parseChainInput options.chain)
  let owner ← match options.ownerKeyFile, options.owner with
    | none, none => do
      let source ← NativeSigner.resolveKeyFile none none
        { options.passwords with nonInteractive := options.nonInteractive }
      NativeSigner.addressFromProtectedFile source
    | none, some ownerRaw => fromExcept (parseOwner ownerRaw)
    | some file, expected => do
      let source ← NativeSigner.resolveKeyFile (some file) none
        { options.passwords with nonInteractive := options.nonInteractive }
      let derived ← NativeSigner.addressFromProtectedFile source
      if let some raw := expected then
        if (← fromExcept <| parseOwner raw) != derived then
          throw <| IO.userError "Owner key differs from the expected owner address."
      pure derived
  let recipient ← match options.receiver with
    | none => pure owner
    | some raw => fromExcept <| parseOwner raw
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let requestId ← IO.mkRef (1 : Nat)
  let read (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params
  let review ← inspectWith chain owner recipient read
  fromExcept (render review)

end Tornado.Cli.SmartAccountRecover
