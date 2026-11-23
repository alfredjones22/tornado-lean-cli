import Lean
import Tornado.Cli.History
import Tornado.Crypto.SHA256
import Tornado.Crypto.Keccak
import Tornado.Domain.ChainInput
import Tornado.Runtime.ProtectedIO

/-!
Native read-only one-note withdrawal review. `--dry-run` matches the pinned
TypeScript command's no-network, no-proof review. `--preflight` is an extra
read-only mode: it checks the selected deposit, pool history, receipt and
exact-block `isSpent` claim through the native history engine. Neither path
constructs a proof, fee quote, signature, UserOperation, status file, or
submission. A no-flag invocation fails closed instead of acting like SEND.
-/

namespace Tornado.Cli.WithdrawOne

open Lean Tornado.Crypto Tornado.Domain Tornado.Runtime

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => fail message

private structure Options where
  noteFile : Option String := none
  recipient : Option String := none
  noteIndex : Option String := none
  chain : String := "1"
  route : String := "4337"
  rpc : Option String := none
  bundler : Option String := none
  assetsDir : Option String := none
  cacheDir : Option String := none
  statusDir : String := "."
  retryRejected : Bool := false
  dryRun : Bool := false
  preflight : Bool := false
  yes : Bool := false
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--dry-run" :: rest => parseOptions rest { options with dryRun := true }
  | "--preflight" :: rest => parseOptions rest { options with preflight := true }
  | "--retry-rejected" :: rest => parseOptions rest { options with retryRejected := true }
  | "--yes" :: rest => parseOptions rest { options with yes := true }
  | "--note-file" :: value :: rest => parseOptions rest { options with noteFile := some value }
  | "--recipient" :: value :: rest => parseOptions rest { options with recipient := some value }
  | "--note-index" :: value :: rest => parseOptions rest { options with noteIndex := some value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--route" :: value :: rest => parseOptions rest { options with route := value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: value :: rest => parseOptions rest { options with bundler := some value }
  | "--assets-dir" :: value :: rest => parseOptions rest { options with assetsDir := some value }
  | "--history-cache-dir" :: value :: rest => parseOptions rest { options with cacheDir := some value }
  | "--status-dir" :: value :: rest => parseOptions rest { options with statusDir := value }
  | ["--note-file"] | ["--recipient"] | ["--note-index"] | ["--chain"] |
    ["--route"] | ["--rpc"] | ["--bundler-url"] | ["--assets-dir"] |
    ["--status-dir"] | ["--history-cache-dir"] => .error "Withdrawal option is missing its value."
  | argument :: rest =>
    if argument.startsWith "--note-file=" then
      parseOptions rest { options with noteFile := some (String.ofList (argument.toList.drop 12)) }
    else if argument.startsWith "--recipient=" then
      parseOptions rest { options with recipient := some (String.ofList (argument.toList.drop 12)) }
    else if argument.startsWith "--note-index=" then
      parseOptions rest { options with noteIndex := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--chain=" then
      parseOptions rest { options with chain := String.ofList (argument.toList.drop 8) }
    else if argument.startsWith "--route=" then
      parseOptions rest { options with route := String.ofList (argument.toList.drop 8) }
    else if argument.startsWith "--rpc=" then
      parseOptions rest { options with rpc := some (String.ofList (argument.toList.drop 6)) }
    else if argument.startsWith "--bundler-url=" then
      parseOptions rest { options with bundler := some (String.ofList (argument.toList.drop 14)) }
    else if argument.startsWith "--assets-dir=" then
      parseOptions rest { options with assetsDir := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--history-cache-dir=" then
      parseOptions rest { options with cacheDir := some (String.ofList (argument.toList.drop 20)) }
    else if argument.startsWith "--status-dir=" then
      parseOptions rest { options with statusDir := String.ofList (argument.toList.drop 13) }
    else .error s!"error: unknown option '{argument}'"

private def help : String :=
  "Usage: tornado withdraw one --note-file <path> --recipient <address> [options]\n\n" ++
  "Review one selected note without signing or submitting.\n\n" ++
  "Options:\n" ++
  "  --dry-run              Local review; no network or proof\n" ++
  "  --preflight            Read-only pool history and spent check (discloses nullifier hash to RPC)\n" ++
  "  --route <route>        4337 or relayer (default: 4337)\n" ++
  "  --note-index <n>       1-based position in a multi-note backup\n" ++
  "  --chain <id>           Ethereum chain ID (default: 1)\n" ++
  "  --rpc <url>            Chain RPC for preflight\n" ++
  "  --bundler-url <url>    Bundler shown in the 4337 review\n" ++
  "  --assets-dir <path>    Pinned offline history asset directory\n" ++
  "  --history-cache-dir <path>  Existing private directory for checked history cache\n" ++
  "  --status-dir <path>    Directory of a future opaque status file\n" ++
  "  -h, --help             Display this help\n"

private def asciiHex (char : Char) : Bool :=
  ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f') ||
    ('A' ≤ char && char ≤ 'F')

private def nibble (char : Char) : Nat :=
  if '0' ≤ char && char ≤ '9' then char.toNat - '0'.toNat
  else if 'a' ≤ char && char ≤ 'f' then char.toNat - 'a'.toNat + 10
  else char.toNat - 'A'.toNat + 10

/-- Viem's `getAddress` presentation and mixed-case EIP-55 guard. Plain
    lowercase/uppercase forms are accepted and rendered in checksum case. -/
def checkedRecipient (raw : String) : Except String String := do
  if !raw.startsWith "0x" || raw.length != 42 ||
      !(raw.toList.drop 2).all asciiHex then
    throw "Recipient must be a nonzero Ethereum address."
  let digits := String.ofList (raw.toList.drop 2)
  let bytes ← parseHexBytes raw
  if bytes.size != 20 || bytes.data.all (· == 0) then
    throw "Recipient must be a nonzero Ethereum address."
  let lower := digits.toLower
  let hash := bytesToHex (keccak256 lower.toUTF8)
  let checksum := String.ofList ((List.range 40).map fun index =>
    let char := lower.toList[index]!
    if 'a' ≤ char && char ≤ 'f' && nibble hash.toList[index]! ≥ 8 then
      char.toUpper else char)
  if digits != lower && digits != digits.toUpper && digits != checksum then
    throw "Recipient has an invalid mixed-case checksum."
  return "0x" ++ checksum

private def endpointHostname (raw : String) : Except String String := do
  let url := jsTrim raw
  let (https, rest) ←
    if url.startsWith "https://" then
      pure (true, String.ofList (url.toList.drop 8))
    else if url.startsWith "http://" then
      pure (false, String.ofList (url.toList.drop 7))
    else throw "Use HTTPS or a local HTTP endpoint."
  let authority := String.ofList (rest.toList.takeWhile
    (fun char => char != '/' && char != '?' && char != '#'))
  if authority.isEmpty || authority.contains '@' || authority.contains '\\' ||
      authority.contains ' ' then
    throw "Enter a complete endpoint URL without credentials."
  let hostname ← if authority.startsWith "[" then
      let parts := authority.splitOn "]"
      match parts with
      | [host, suffix] =>
        if suffix != "" && !suffix.startsWith ":" then
          throw "Invalid endpoint host."
        pure (host ++ "]")
      | _ => throw "Invalid endpoint host."
    else pure <| (authority.splitOn ":").head!
  if hostname.isEmpty || !hostname.toList.all
      (fun char => char.toNat > 32 && char.toNat < 127) then
    throw "Invalid endpoint host."
  if !https && !(hostname.toLower == "localhost" || hostname == "127.0.0.1" ||
      hostname == "[::1]") then
    throw "Use HTTPS or a local HTTP endpoint."
  return hostname.toLower

private def resolvePath (current : System.FilePath) (raw : String) : String := Id.run do
  let absolute := if (System.FilePath.mk raw).isAbsolute then raw
    else current.toString ++ "/" ++ raw
  let mut parts : List String := []
  for part in absolute.splitOn "/" do
    if part.isEmpty || part == "." then continue
    if part == ".." then parts := parts.dropLast
    else parts := parts ++ [part]
  return "/" ++ String.intercalate "/" parts

/-- Byte-for-byte TS status-file label: HMAC-SHA256 keyed by the 31-byte
    nullifier secret, over a pool-scoped static label. Directory listings do
    not reveal the note's public nullifier hash. -/
def statusFileName (note : ParsedNote) : Except String String := do
  if note.preimage.length != 124 then throw "Invalid selected note preimage."
  let nullifierSecret ← parseHexBytes (String.ofList (note.preimage.toList.take 62))
  if nullifierSecret.size != 31 then throw "Invalid selected note preimage."
  let chainId := chainNumber note.pool.chainId
  let label := s!"tornado-cli-new-era/withdrawal-status/v1/{chainId}/{note.pool.asset.symbol.toLower}/{note.pool.denomination}"
  let digest := hmacSHA256Hex nullifierSecret label.toUTF8
  return s!"tornado-withdraw-{chainId}-{digest}.json"

private def readSelected (path : String) (chain : ChainId)
    (index : Option String) : IO BackupIdentity := do
  let current ← IO.currentDir
  let absolute := resolvePath current path
  let bytes ← ProtectedIO.readPrivate absolute
  let some contents := String.fromUTF8? bytes
    | fail "Private note backup is not UTF-8."
  checked (Tornado.Cli.History.selectNote contents chain index)

private def defaultBundler (chain : ChainId) : String :=
  s!"https://public.pimlico.io/v2/{chainNumber chain}/rpc"

private def routeName (route : String) : String :=
  if route == "relayer" then "Classic TORN relayer" else "4337 paymaster"

private def reviewLines (note : BackupIdentity) (recipient statusPath
    bundlerHost route : String) : List String :=
  [s!"Route: {routeName route}",
   s!"Recipient: {recipient}",
   s!"Pool: {note.note.pool.denomination} {note.note.pool.asset.symbol} ({note.note.pool.address})",
   s!"Note value: {formatUnitsExact note.note.pool.amount note.note.pool.asset.decimals} {note.note.pool.asset.symbol}"] ++
  (if route == "4337" then [s!"Bundler host: {bundlerHost}"] else []) ++
  [s!"Status file if submitted: {statusPath}"]

/-- Pure local review output from an already protected-selected note. -/
def dryRunReview (note : BackupIdentity) (recipient statusPath bundlerHost route : String) :
    String :=
  String.intercalate "\n" (reviewLines note recipient statusPath bundlerHost route ++
    ["Dry run complete. No proof, fee quote, signature or UserOperation was created."]) ++ "\n"

/-- Convert the checked native history report to a narrow preflight review.
    This checks the selected pool and commitment again rather than treating
    an arbitrary JSON object as evidence for the selected note. -/
def preflightSummary (note : BackupIdentity) (recipient statusPath bundlerHost route
    reportText : String) : Except String String := do
  let report ← Json.parse reportText
  let pool ← report.getObjVal? "pool"
  let address ← (← pool.getObjVal? "address").getStr?
  let commitment ← (← report.getObjVal? "commitment").getStr?
  if address.toLower != note.note.pool.address.toLower ||
      commitment.toLower != note.publicIdentity.commitment.toLower then
    throw "Preflight report differs from the selected note or pool."
  let checkedResult ← report.getObjVal? "checked"
  let spent ← (← checkedResult.getObjVal? "spent").getBool?
  if spent then throw "This selected note is already spent."
  let block ← (← checkedResult.getObjVal? "blockNumber").getStr?
  let deposit ← report.getObjVal? "deposit"
  let depositBlock ← (← deposit.getObjVal? "blockNumber").getStr?
  let some blockNumber := block.toNat?
    | throw "Preflight checked block is not decimal."
  let some depositNumber := depositBlock.toNat?
    | throw "Preflight deposit block is not decimal."
  if depositNumber > blockNumber then
    throw "Preflight deposit is newer than the checked block."
  return String.intercalate "\n" (reviewLines note recipient statusPath bundlerHost route ++
    [s!"Deposit verified at block {depositBlock}.",
     s!"Unspent at checked block {block}.",
     "Preflight complete. No proof, fee quote, signature or UserOperation was created."]) ++ "\n"

/-- Read-only network preflight. It deliberately does not return any proof
    material or fee quote and refuses a note that is already spent. -/
def preflightWith (transport : HistorySync.Transport) (note : BackupIdentity)
    (recipient statusPath bundlerHost route : String)
    (assetsDir cacheDir : Option String := none) : IO String := do
  let reportText ← Tornado.Cli.History.inspectJson transport note assetsDir cacheDir
  checked (preflightSummary note recipient statusPath bundlerHost route reportText)

/-- Runnable command: `--dry-run` is offline; `--preflight` performs read-only
    network checks. No branch signs, reserves a status file, or broadcasts. -/
def withdrawOneCommand (args : List String) : IO String := do
  let options ← checked (parseOptions args)
  if options.showHelp then return help
  if options.route != "4337" && options.route != "relayer" then
    fail "Use --route 4337 or --route relayer."
  if options.route == "relayer" && options.retryRejected then
    fail "--retry-rejected is only available for the direct 4337 route."
  if options.dryRun == options.preflight then
    fail "Choose exactly one read-only mode: --dry-run or --preflight. Native withdrawal signing and submission are disabled."
  let some file := options.noteFile
    | fail "error: required option '--note-file <path>' not specified"
  let some rawRecipient := options.recipient
    | fail "error: required option '--recipient <address>' not specified"
  let chain ← checked (parseChainInput options.chain)
  let note ← readSelected file chain options.noteIndex
  if options.route == "relayer" && !supportsClassicRelayer note.note.pool then
    fail "Classic TORN relayers support only original Tornado pools; use --route 4337 for this note."
  let recipient ← checked (checkedRecipient rawRecipient)
  let bundlerRaw ← if let some raw := options.bundler then pure raw
    else if let some raw ← IO.getEnv "TORNADO_BUNDLER_URL" then pure raw
    else pure (defaultBundler chain)
  let bundlerHost ← checked (endpointHostname bundlerRaw)
  if let some rpc := options.rpc then
    let _ ← checked (endpointHostname rpc)
  let current ← IO.currentDir
  let statusPath := resolvePath current options.statusDir ++ "/" ++
    (← checked (statusFileName note.note))
  if options.dryRun then
    return dryRunReview note recipient statusPath bundlerHost options.route
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let _ ← checked (endpointHostname rpc)
  let transport ← checked (HistorySync.liveTransport (chainNumber chain) rpc)
  preflightWith transport note recipient statusPath bundlerHost options.route
    (options.assetsDir.map (resolvePath current)) (options.cacheDir.map (resolvePath current))

end Tornado.Cli.WithdrawOne
