import Lean
import Tornado.Cli.WithdrawOne
import Tornado.Cli.SmartAccountShow
import Tornado.Cli.DepositSend
import Tornado.Runtime.NativeSigner
import Tornado.Protocol.Abi
import Tornado.Protocol.ImportedAbi
import Tornado.Runtime.HttpTransport

/-!
Native `withdraw batch --dry-run` review. Protected notes and owner key are
read locally; the owner address is derived without signing. The selected RPC
is used only to check the pinned SimpleAccount factory/implementation and
current account identity. Raw JSON and Safe Transaction Builder v1.0 calls
are validated, ABI-encoded when needed and hashed in their original order.
No proof, fee quote, signature, UserOperation, journal, or broadcast exists.
-/

namespace Tornado.Cli.WithdrawBatch

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Cli.SmartAccountShow Tornado.SmartAccount

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => fail message

private structure Options where
  notesFile : Option String := none
  ownerKeyFile : Option String := none
  receiver : Option String := none
  contractCalls : Option String := none
  chain : String := "1"
  rpc : Option String := none
  bundler : Option String := none
  simulationRpc : Option String := none
  assetsDir : Option String := none
  cacheDir : Option String := none
  provingRoot : Option String := none
  statusDir : String := "."
  dryRun : Bool := false
  yes : Bool := false
  nonInteractive : Bool := false
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--dry-run" :: rest => parseOptions rest { options with dryRun := true }
  | "--yes" :: rest => parseOptions rest { options with yes := true }
  | "--non-interactive" :: rest => parseOptions rest { options with nonInteractive := true }
  | "--notes-file" :: value :: rest | "--note-file" :: value :: rest =>
    parseOptions rest { options with notesFile := some value }
  | "--owner-key-file" :: value :: rest => parseOptions rest { options with ownerKeyFile := some value }
  | "--receiver" :: value :: rest | "--recipient" :: value :: rest =>
    parseOptions rest { options with receiver := some value }
  | "--contract-calls" :: value :: rest => parseOptions rest { options with contractCalls := some value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: value :: rest => parseOptions rest { options with bundler := some value }
  | "--simulation-rpc" :: value :: rest => parseOptions rest { options with simulationRpc := some value }
  | "--assets-dir" :: value :: rest => parseOptions rest { options with assetsDir := some value }
  | "--history-cache-dir" :: value :: rest => parseOptions rest { options with cacheDir := some value }
  | "--proving-assets-root" :: value :: rest => parseOptions rest { options with provingRoot := some value }
  | "--status-dir" :: value :: rest => parseOptions rest { options with statusDir := value }
  | ["--notes-file"] | ["--note-file"] | ["--owner-key-file"] | ["--receiver"] | ["--recipient"] |
    ["--contract-calls"] | ["--chain"] | ["--rpc"] |
    ["--bundler-url"] | ["--simulation-rpc"] | ["--assets-dir"] |
    ["--history-cache-dir"] | ["--proving-assets-root"] |
    ["--status-dir"] => .error "Batch withdrawal option is missing its value."
  | argument :: rest =>
    if argument.startsWith "--notes-file=" then
      parseOptions rest { options with notesFile := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--note-file=" then
      parseOptions rest { options with notesFile := some (String.ofList (argument.toList.drop 12)) }
    else if argument.startsWith "--owner-key-file=" then
      parseOptions rest { options with ownerKeyFile := some (String.ofList (argument.toList.drop 17)) }
    else if argument.startsWith "--receiver=" then
      parseOptions rest { options with receiver := some (String.ofList (argument.toList.drop 11)) }
    else if argument.startsWith "--recipient=" then
      parseOptions rest { options with receiver := some (String.ofList (argument.toList.drop 12)) }
    else if argument.startsWith "--contract-calls=" then
      parseOptions rest { options with contractCalls := some (String.ofList (argument.toList.drop 17)) }
    else if argument.startsWith "--chain=" then
      parseOptions rest { options with chain := String.ofList (argument.toList.drop 8) }
    else if argument.startsWith "--rpc=" then
      parseOptions rest { options with rpc := some (String.ofList (argument.toList.drop 6)) }
    else if argument.startsWith "--bundler-url=" then
      parseOptions rest { options with bundler := some (String.ofList (argument.toList.drop 14)) }
    else if argument.startsWith "--simulation-rpc=" then
      parseOptions rest { options with simulationRpc := some (String.ofList (argument.toList.drop 17)) }
    else if argument.startsWith "--assets-dir=" then
      parseOptions rest { options with assetsDir := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--history-cache-dir=" then
      parseOptions rest { options with cacheDir := some (String.ofList (argument.toList.drop 20)) }
    else if argument.startsWith "--proving-assets-root=" then
      parseOptions rest { options with provingRoot := some (String.ofList (argument.toList.drop 22)) }
    else if argument.startsWith "--status-dir=" then
      parseOptions rest { options with statusDir := String.ofList (argument.toList.drop 13) }
    else .error s!"error: unknown option '{argument}'"

private def help : String :=
  "Usage: tornado withdraw batch --notes-file <path> [--owner-key-file <path>] --dry-run [options]\n\n" ++
  "Review 1–12 same-asset notes, the pinned smart account, receiver and ordered calls.\n" ++
  "--note-file is an alias for --notes-file; --recipient is an alias for --receiver.\n" ++
  "Without contract calls, proceeds are forwarded to the selected receiver (default: smart account).\n" ++
  "--non-interactive accepts unattended review and requires --owner-key-file.\n" ++
  "--assets-dir, --history-cache-dir and --proving-assets-root are accepted for live-command consistency; dry-run does not load history or proving assets.\n" ++
  "One note requires at least one contract call; otherwise select 2–12 notes.\n" ++
  "No proof, fee quote, signature or UserOperation is created.\n"

private def resolvePath (current : System.FilePath) (raw : String) : String := Id.run do
  let absolute := if (System.FilePath.mk raw).isAbsolute then raw
    else current.toString ++ "/" ++ raw
  let mut parts : List String := []
  for part in absolute.splitOn "/" do
    if part.isEmpty || part == "." then continue
    if part == ".." then parts := parts.dropLast
    else parts := parts ++ [part]
  return "/" ++ String.intercalate "/" parts

private def checkedEndpoint (raw : String) : Except String String := do
  let url := jsTrim raw
  let (secure, rest) ←
    if url.startsWith "https://" then pure (true, String.ofList (url.toList.drop 8))
    else if url.startsWith "http://" then pure (false, String.ofList (url.toList.drop 7))
    else throw "Use HTTPS or a local HTTP endpoint."
  let authority := String.ofList (rest.toList.takeWhile
    (fun char => char != '/' && char != '?' && char != '#'))
  if authority.isEmpty || authority.contains '@' || authority.contains '\\' ||
      authority.contains ' ' then
    throw "Enter a complete endpoint URL without credentials."
  let host := if authority.startsWith "[" then
      "[" ++ ((String.ofList (authority.toList.drop 1)).splitOn "]").head! ++ "]"
    else (authority.splitOn ":").head!
  if host.isEmpty || (!secure && host.toLower != "localhost" &&
      host != "127.0.0.1" && host != "[::1]") then
    throw "Use HTTPS or a local HTTP endpoint."
  return url

private def readProtectedText (path : String) : IO String := do
  let current ← IO.currentDir
  let bytes ← ProtectedIO.readPrivate (resolvePath current path)
  let some contents := String.fromUTF8? bytes
    | fail "Protected input file is not UTF-8."
  return contents

private def decimalValue (raw : String) : Except String Nat := do
  if raw.isEmpty || !raw.toList.all (fun char => '0' ≤ char && char ≤ '9') then
    throw "Contract call value must be an integer string in wei."
  let some value := raw.toNat?
    | throw "Contract call value is too large."
  if value >= Abi.maxUint256 then
    throw "Contract call value must be a uint256 amount of wei."
  return value

private def addressNat (raw : String) : Except String Nat := do
  match parseOwner raw with
  | .ok address => .ok address
  | .error _ => .error "Invalid contract call target."

private def parseCall (json : Json) : Except String Abi.ContractCall := do
  if let .ok operation := json.getObjVal? "operation" then
    if operation != toJson (0 : Nat) && operation != toJson ("0" : String) then
      throw "Only ordinary CALL operations are supported; delegatecall is disabled."
  let to ← addressNat (← (← json.getObjVal? "to").getStr?)
  let value ← decimalValue (← (← json.getObjVal? "value").getStr?)
  let data ← match json.getObjVal? "contractMethod" with
    | .ok method =>
      if method != Json.null then do
        let values := (json.getObjVal? "contractInputsValues").toOption.getD .null
        let encoded ← ImportedAbi.encodeFunctionData method values value
        if let .ok supplied := json.getObjVal? "data" then
          if supplied != .null then
            let raw ← supplied.getStr?
            if raw.toLower != "0x" ++ bytesToHex encoded then
              throw "Imported ABI arguments and calldata disagree."
        pure encoded
      else do
        let raw ← (← json.getObjVal? "data").getStr?
        if !raw.startsWith "0x" || raw.length % 2 != 0 then
          throw "Contract call data must be even-length hex."
        parseHexBytes raw
    | .error _ => do
      let raw ← (← json.getObjVal? "data").getStr?
      if !raw.startsWith "0x" || raw.length % 2 != 0 then
        throw "Contract call data must be even-length hex."
      parseHexBytes raw
  return { to, value, data }

/-- Raw call arrays and Safe Transaction Builder v1.0 files. Imported method
arguments are natively re-encoded and any supplied calldata must agree. -/
def parseContractCalls (text : String) (chainId : ChainId) :
    Except String (Array Abi.ContractCall) := do
  if jsUtf16Length text > 512000 then
    throw "Contract call JSON exceeds 512 KiB."
  let input ← Json.parse text |>.mapError (fun _ => "Contract calls must be valid JSON.")
  let values ← match input with
    | .arr rows => pure rows
    | .obj _ => do
      let version ← (← input.getObjVal? "version").getStr?
      let chain ← input.getObjVal? "chainId"
      let chainText ← match chain with
        | .str value => pure value
        | .num _ => pure chain.compress
        | _ => throw "Expected a Safe batch v1.0 for the selected chain."
      if version != "1.0" || chainText != toString (chainNumber chainId) then
        throw "Expected a Safe batch v1.0 for the selected chain."
      (← input.getObjVal? "transactions").getArr?
    | _ => throw "Expected an array of contract calls or a Safe batch v1.0."
  if values.isEmpty then throw "Provide at least one contract call."
  if values.size > Abi.maxContractCalls then
    throw s!"Use up to {Abi.maxContractCalls} contract calls."
  let calls ← values.mapM parseCall
  Abi.validateCalls calls

structure Scope where
  account : SmartAccountShow.Account
  recipient : Nat
  calls : Array Abi.ContractCall
  callsHash : ByteArray
  deriving Inhabited

/-- Pure scope checks before rendering the selected account's post-withdrawal
    actions. `Abi.validateCalls` protects recovery by excluding self-calls. -/
def makeScope (account : SmartAccountShow.Account) (receiver : Option Nat)
    (calls : Array Abi.ContractCall) : Except String Scope := do
  if account.owner == 0 || account.address == 0 ||
      account.owner >= Abi.maxAddress || account.address >= Abi.maxAddress then
    throw "Invalid selected smart-account identity."
  let recipient := receiver.getD account.address
  if recipient == 0 || recipient >= Abi.maxAddress then
    throw "Enter a nonzero receiver address."
  let validated ← Abi.validateCalls calls (some account.address)
  if !validated.isEmpty && recipient != account.address then
    throw "An external --receiver cannot be combined with --contract-calls. Keep proceeds in the smart account."
  let hash ← Abi.callsHash validated
  return { account := account, recipient := recipient, calls := validated, callsHash := hash }

private def natFromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Same pinned factory, implementation, EntryPoint, deployed owner and
    implementation-slot checks as `smart-account show`, on one captured block.
    The RPC remains an external chain-truth assumption. -/
def loadAccountWith (chainId : ChainId) (owner : Nat)
    (read : JsonRpc.Method → Array Json → IO Json) : IO SmartAccountShow.Account := do
  let ownerText ← checked (checksumAddress owner)
  let chain ← checked (decodeQuantityResult (← read .chainId #[]))
  if chain != chainNumber chainId then fail "The RPC endpoint is on a different network."
  let block ← checked ((← read .blockNumber #[]).getStr?)
  let _ ← checked (JsonRpc.parseHexQuantity block)
  let factoryCode ← checked <| decodeCodeResult
    (← read .getCode (codeParams simpleAccountFactory block))
  if !pinnedFactoryCode factoryCode then
    fail "The pinned SimpleAccount v0.8 factory is unavailable."
  let ownerCode ← checked <| decodeCodeResult
    (← read .getCode (codeParams ownerText block))
  if !ownerCodeAllowed ownerCode then
    fail "Contract-wallet owners are not supported for this smart account."
  let implementation ← checked <| decodeAddressResult
    (← read .call (callParams simpleAccountFactory
      (Abi.selector "accountImplementation()") block))
  let accountAddress ← checked <| decodeAddressResult
    (← read .call (callParams simpleAccountFactory
      (← checked (getAddressData owner)) block))
  let implementationText ← checked (checksumAddress implementation)
  let accountText ← checked (checksumAddress accountAddress)
  let implementationCode ← checked <| decodeCodeResult
    (← read .getCode (codeParams implementationText block))
  let implementationEntryPoint ← checked <| decodeAddressResult
    (← read .call (callParams implementationText
      (Abi.selector "entryPoint()") block))
  let accountCode ← checked <| decodeCodeResult
    (← read .getCode (codeParams accountText block))
  let entryPointNonce ← checked <| decodeUintResult
    (← read .call (callParams entryPoint
      (Abi.selector "getNonce(address,uint192)" ++
        (← checked (Abi.addressWord accountAddress)) ++
        (← checked (Abi.uintWord 0))) block))
  let mut actualOwner : Option Nat := none
  let mut actualEntryPoint : Option Nat := none
  let mut slotValue : Option Nat := none
  if !accountCode.isEmpty then
    actualOwner := some (← checked <| decodeAddressResult
      (← read .call (callParams accountText (Abi.selector "owner()") block)))
    actualEntryPoint := some (← checked <| decodeAddressResult
      (← read .call (callParams accountText (Abi.selector "entryPoint()") block)))
    slotValue := some (← checked <| decodeSlotResult
      (← read .getStorageAt (slotParams accountText block)))
  checked <| validateIdentity {
    owner := owner, factoryCode := factoryCode, ownerCode := ownerCode,
    implementation := implementation, implementationCode := implementationCode,
    implementationEntryPoint := implementationEntryPoint,
    account := accountAddress, accountCode := accountCode,
    nonce := entryPointNonce, actualOwner := actualOwner,
    actualEntryPoint := actualEntryPoint, slotValue := slotValue }

private def renderCall (index : Nat) (call : Abi.ContractCall) : Except String String := do
  let target ← checksumAddress call.to
  let hex := "0x" ++ bytesToHex call.data
  let calldataPrefix := String.ofList (hex.toList.take 10)
  let hash := "0x" ++ bytesToHex (keccak256 call.data)
  return s!"{index + 1}. {target} · {call.value} wei · calldata {calldataPrefix} ({call.data.size} bytes; {hash})"

/-- Human review matches the TypeScript dry-run line order, including the
    ordered hash and each call's calldata prefix, byte length, and full hash. -/
def render (notes : List ParsedNote) (scope : Scope) (statusDirectory : String) :
    Except String String := do
  let rebuilt ← makeScope scope.account (some scope.recipient) scope.calls
  if rebuilt.callsHash != scope.callsHash then
    throw "Reviewed contract calls changed after scope construction."
  if notes.isEmpty || notes.length > maxMultiNotes ||
      notes.length < (if scope.calls.isEmpty then 2 else 1) ||
      notes.any (fun note => note.pool.asset.symbol != notes.head!.pool.asset.symbol) then
    throw "Invalid selected note batch for this call scope."
  let owner ← checksumAddress scope.account.owner
  let account ← checksumAddress scope.account.address
  let receiver ← checksumAddress scope.recipient
  let asset := notes.head!.pool.asset
  let total := notes.foldl (fun sum note => sum + note.pool.amount) 0
  let mut lines := [s!"Owner: {owner}", s!"Smart account: {account}",
    s!"Notes: {notes.length}",
    s!"Total note value: {formatUnitsExact total asset.decimals} {asset.symbol}",
    s!"Receiver: {receiver}", s!"Contract calls: {scope.calls.size}"]
  if !scope.calls.isEmpty then
    lines := lines ++ [s!"Ordered contract-calls hash: 0x{bytesToHex scope.callsHash}"]
    for i in [0:scope.calls.size] do
      lines := lines ++ [← renderCall i scope.calls[i]!]
  lines := lines ++ [s!"Status directory: {statusDirectory}",
    "Dry run complete. No proof, fee quote, signature or UserOperation was created."]
  return String.intercalate "\n" lines ++ "\n"

/-- Runnable read-only command. The owner key and note backup are protected
    inputs; no secret values enter RPC parameters or output. -/
def withdrawBatchCommand (args : List String) : IO String := do
  let options ← checked (parseOptions args)
  if options.showHelp then return help
  if !options.dryRun then
    fail "Native batch withdrawal signing and submission are disabled; use --dry-run."
  let some notesFile := options.notesFile
    | fail "error: required option '--notes-file <path>' not specified"
  if options.nonInteractive && options.ownerKeyFile.isNone then
    fail "--non-interactive requires --owner-key-file for batch withdrawals."
  let keyFile ← NativeSigner.resolveKeyFile options.ownerKeyFile
  let chain ← checked (parseChainInput options.chain)
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc ← checked (checkedEndpoint
    ((options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)))
  let environmentBundler ← IO.getEnv "TORNADO_BUNDLER_URL"
  let bundler := (options.bundler.orElse (fun _ => environmentBundler)).getD
    s!"https://public.pimlico.io/v2/{chainNumber chain}/rpc"
  let _ ← checked (checkedEndpoint bundler)
  let notesText ← readProtectedText notesFile
  let extracted ← checked (extractNoteStrings notesText)
  let current ← IO.currentDir
  let ownerAddress ← NativeSigner.addressFromProtectedFile (resolvePath current keyFile)
  let calls ← match options.contractCalls with
    | none => pure #[]
    | some path => checked (parseContractCalls (← readProtectedText path) chain)
  let notes ← checked (parseBatchNotes (String.intercalate "\n" extracted) chain
    (if calls.isEmpty then 2 else 1))
  let receiver ← match options.receiver with
    | none => pure none
    | some raw =>
      let parsed ← checked (WithdrawOne.checkedRecipient raw)
      let bytes ← checked (parseHexBytes parsed)
      pure (some (natFromBytes bytes))
  let requestId ← IO.mkRef (1 : Nat)
  let read (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params
  let account ← loadAccountWith chain ownerAddress read
  let scope ← checked (makeScope account receiver calls)
  let current ← IO.currentDir
  checked (render notes scope (resolvePath current options.statusDir))

end Tornado.Cli.WithdrawBatch
