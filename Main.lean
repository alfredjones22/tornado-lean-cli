import Tornado.Domain.Plan
import Tornado.Domain.ChainInput
import Tornado.Policy
import Tornado.Domain.DepositBackup
import Tornado.Runtime.ProtectedIO
import Tornado.Runtime.Entropy
import Tornado.Cli.NoteCreate
import Tornado.Cli.SmartAccountShow
import Tornado.Cli.SmartAccountStatus
import Tornado.Cli.SmartAccountRecover
import Tornado.Cli.DepositStatus
import Tornado.Cli.DepositResume
import Tornado.Cli.DepositStatusCommand
import Tornado.Cli.WithdrawalStatusCommand
import Tornado.Cli.RelayerWithdrawalStatus
import Tornado.Cli.BatchWithdrawalStatus
import Tornado.Cli.History
import Tornado.Cli.DepositSend
import Tornado.Cli.DepositMulti
import Tornado.Cli.DepositMultiSend
import Tornado.Cli.DepositBatch7702
import Tornado.Cli.WithdrawOne
import Tornado.Cli.WithdrawBatch
import Tornado.Cli.SponsoredWithdraw
import Tornado.Cli.RecoverySend

namespace Tornado.Cli

open Tornado.Domain

structure Options where
  chain : String := "1"
  asset : Option String := none
  amount : Option String := none
  excluded : List String := []
  positionals : Nat := 0
  unknownOption : Option String := none
  showHelp : Bool := false
  deriving Inhabited

private def variadicContinuation (value : String) : Bool :=
  !value.startsWith "-" ||
    (value.startsWith "-" &&
      ((value.toList.drop 1).head?.any (fun c => c.isDigit || c == '.')))

private partial def parseOptions (args : List String) (options : Options)
    (plan : Bool) : Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ => .ok { options with showHelp := true }
  | "--help" :: _ => .ok { options with showHelp := true }
  | "--chain" :: value :: rest =>
      parseOptions rest { options with chain := value } plan
  | ["--chain"] => .error "error: option '--chain <id>' argument missing"
  | "--asset" :: value :: rest =>
      parseOptions rest { options with asset := some value } plan
  | ["--asset"] => .error "error: option '--asset <symbol>' argument missing"
  | "--amount" :: value :: rest =>
      if !plan then parseOptions (value :: rest)
        { options with unknownOption := options.unknownOption.orElse (fun _ => some "--amount") } plan
      else parseOptions rest { options with amount := some value } plan
  | ["--amount"] =>
      if plan then .error "error: option '--amount <amount>' argument missing"
      else .ok { options with unknownOption := options.unknownOption.orElse (fun _ => some "--amount") }
  | "--exclude" :: first :: rest =>
      if !plan then parseOptions (first :: rest)
        { options with unknownOption := options.unknownOption.orElse (fun _ => some "--exclude") } plan
      else
        let following := rest.takeWhile variadicContinuation
        parseOptions (rest.drop following.length)
          { options with excluded := options.excluded ++ (first :: following) } plan
  | ["--exclude"] =>
      if plan then .error "error: option '--exclude <denominations...>' argument missing"
      else .ok { options with unknownOption := options.unknownOption.orElse (fun _ => some "--exclude") }
  | "--" :: rest =>
      .ok { options with positionals := options.positionals + rest.length }
  | argument :: rest =>
      if argument.startsWith "--chain=" then
        parseOptions rest { options with chain := String.ofList (argument.toList.drop 8) } plan
      else if argument.startsWith "--asset=" then
        parseOptions rest { options with asset := some (String.ofList (argument.toList.drop 8)) } plan
      else if argument.startsWith "--amount=" then
        if !plan then .error s!"error: unknown option '{argument}'"
        else parseOptions rest { options with amount := some (String.ofList (argument.toList.drop 9)) } plan
      else if argument.startsWith "--exclude=" then
        if !plan then parseOptions rest
          { options with unknownOption := options.unknownOption.orElse (fun _ => some argument) } plan
        else
          let following := rest.takeWhile variadicContinuation
          parseOptions (rest.drop following.length)
            { options with excluded := options.excluded ++ (String.ofList (argument.toList.drop 10) :: following) } plan
      else if argument.startsWith "-" then
        parseOptions rest { options with unknownOption := options.unknownOption.orElse (fun _ => some argument) } plan
      else parseOptions rest { options with positionals := options.positionals + 1 } plan

private def selectedChain (raw : String) : Except String ChainId := do
  parseChainInput raw

private def withLines (lines : List String) : String :=
  String.intercalate "\n" lines ++ "\n"

private def poolsHelp : String :=
  "Usage: tornado pools [options]\n\n" ++
  "List SDK-supported Tornado pools\n\n" ++
  "Options:\n" ++
  "  --chain <id>      Ethereum chain ID (default: \"1\")\n" ++
  "  --asset <symbol>  Asset symbol\n" ++
  "  -h, --help        display help for command\n"

private def planHelp : String :=
  "Usage: tornado deposit plan [options]\n\n" ++
  "Find exact denomination plans for an amount\n\n" ++
  "Options:\n" ++
  "  --amount <amount>             Amount in asset units\n" ++
  "  --asset <symbol>              Asset symbol (default: \"ETH\")\n" ++
  "  --chain <id>                  Ethereum chain ID (default: \"1\")\n" ++
  "  --exclude <denominations...>  Exclude denominations\n" ++
  "  -h, --help                    display help for command\n"

def poolsCommand (args : List String) : Except String String := do
  let options ← parseOptions args {} false
  if options.showHelp then return poolsHelp
  if let some unknown := options.unknownOption then
    throw s!"error: unknown option '{unknown}'"
  if options.positionals > 0 then
    throw s!"error: too many arguments for 'pools'. Expected 0 arguments but got {options.positionals}."
  let chain ← selectedChain options.chain
  let pools := poolsFor chain options.asset
  if pools.isEmpty then throw "No supported pools match this asset."
  return withLines (pools.map fun pool => s!"{pool.denomination} {pool.asset.symbol}\t{pool.address}")

def depositPlanCommand (args : List String) : Except String String := do
  let options ← parseOptions args {} true
  if options.showHelp then return planHelp
  let some rawAmount := options.amount | throw "error: required option '--amount <amount>' not specified"
  if let some unknown := options.unknownOption then
    throw s!"error: unknown option '{unknown}'"
  if options.positionals > 0 then
    throw s!"error: too many arguments for 'plan'. Expected 0 arguments but got {options.positionals}."
  let chain ← selectedChain options.chain
  let available := poolsFor chain (some (options.asset.getD "ETH"))
  let some first := available.head?
    | throw "This asset has no supported pools on the selected chain."
  let amount ← parseAmount rawAmount first.asset.decimals
  let excluded ← parseExcludedDenominations options.excluded available
  let allowed := available.filter (fun pool => !excluded.contains pool.amount)
  let choices ← denominationPlanChoices amount allowed
  if choices.isEmpty then
    let _ ← requireDenominationPlan amount allowed
    throw "No exact Tornado packing is possible with these pool exclusions."
  for choice in choices do
    let _ ← validatePlan amount allowed choice
  let rows := (choices.zipIdx).flatMap fun (choice, index) =>
    [s!"Plan {index + 1}: {choice.noteCount} notes, up to {choice.batchCount} Simple7702 deposit batch(es) for an undelegated EOA"] ++
    (choice.entries.map fun entry =>
      s!"  {entry.count} × {entry.pool.denomination} {entry.pool.asset.symbol}")
  return withLines (rows ++ ["The sender code and token allowance determine the actual route in deposit send."])

def runReadOnly : List String → Except String String
  | ["pools", "-h"] => .ok poolsHelp
  | ["pools", "--help"] => .ok poolsHelp
  | ["deposit", "plan", "-h"] => .ok planHelp
  | ["deposit", "plan", "--help"] => .ok planHelp
  | "pools" :: rest => poolsCommand rest
  | "deposit" :: "plan" :: rest => depositPlanCommand rest
  | _ => .error "This command is not implemented in the Lean CLI and cannot move funds."

private def help : String :=
  "tornado-lean-cli (native Lean port in progress)\n\n" ++
  "Commands: pools, deposit plan, deposit send, deposit pay-invoice, deposit status, deposit inspect-status, notes create, notes create-plan, notes inspect, notes invoice, withdraw one, withdraw batch, withdraw status, smart-account show, smart-account status, smart-account recover, history, compliance report.\n" ++
  "Sending requires --broadcast and review; --non-interactive explicitly authorizes the reviewed send without a typed prompt. Deposits choose a journal when omitted; recovery requires --journal. Resume uses the original journal. Omit the account key-file option for hidden terminal entry. Use --dry-run for review without sending.\n"

/-- Select a unique visible journal name without creating or overwriting it.
The deposit adapter still performs protected exclusive creation before any
signature can be exposed. Resume always supplies its original journal. -/
private def depositJournalPath (requested : Option String) (chain : ChainId) : IO String := do
  if let some path := requested then return path
  let directory ← IO.currentDir
  let suffix := Tornado.Crypto.bytesToHex (← Tornado.Runtime.Entropy.readKernelRandom 16)
  return (directory / s!"tornado-deposit-{chainNumber chain}-{suffix}.json").toString

private structure InvoiceOptions where
  invoiceFile : Option String := none
  keyFile : Option String := none
  journal : Option String := none
  chain : String := "1"
  rpc : Option String := none
  dryRun : Bool := false
  experimentalSend : Bool := false
  nonInteractive : Bool := false
  help : Bool := false
  deriving Inhabited

private partial def parseInvoiceOptions (args : List String)
    (options : InvoiceOptions := {}) : Except String InvoiceOptions :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--invoice-file" :: value :: rest =>
      parseInvoiceOptions rest { options with invoiceFile := some value }
  | "--key-file" :: value :: rest =>
      parseInvoiceOptions rest { options with keyFile := some value }
  | "--journal" :: value :: rest =>
      parseInvoiceOptions rest { options with journal := some value }
  | "--chain" :: value :: rest =>
      parseInvoiceOptions rest { options with chain := value }
  | "--rpc" :: value :: rest =>
      parseInvoiceOptions rest { options with rpc := some value }
  | "--dry-run" :: rest => parseInvoiceOptions rest { options with dryRun := true }
  | "--broadcast" :: rest =>
      parseInvoiceOptions rest { options with experimentalSend := true }
  | "--non-interactive" :: rest =>
      parseInvoiceOptions rest { options with nonInteractive := true }
  | ["--invoice-file"] | ["--key-file"] | ["--journal"] |
      ["--chain"] | ["--rpc"] =>
      .error "error: option argument missing"
  | item :: rest =>
      if item.startsWith "--invoice-file=" then
        parseInvoiceOptions rest { options with invoiceFile := some (String.ofList (item.toList.drop 15)) }
      else if item.startsWith "--key-file=" then
        parseInvoiceOptions rest { options with keyFile := some (String.ofList (item.toList.drop 11)) }
      else if item.startsWith "--journal=" then
        parseInvoiceOptions rest { options with journal := some (String.ofList (item.toList.drop 10)) }
      else if item.startsWith "--chain=" then
        parseInvoiceOptions rest { options with chain := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--rpc=" then
        parseInvoiceOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else .error s!"error: unknown option '{item}'"

private def invoiceHelp : String :=
  "Usage: tornado deposit pay-invoice --invoice-file <path> [--key-file <path>] [--chain <id>] [--rpc <url>] [--journal <new-path>] (--dry-run | --broadcast)\n" ++
  "Omit --key-file to enter the private key at a hidden terminal prompt.\n" ++
  "Dry run reviews one invoice without signing. Broadcasting requires typing SEND for every reviewed transaction.\n" ++
  "Omit --journal to use a new uniquely named journal in the current directory.\n" ++
  "--non-interactive explicitly authorizes sending without a SEND prompt and requires --key-file. Reviews and validation checks still run.\n"

private def payInvoiceCommand (args : List String) : IO String := do
  let options ← match parseInvoiceOptions args with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  if options.help then return invoiceHelp
  let some invoiceFile := options.invoiceFile
    | throw <| IO.userError "error: required option '--invoice-file <path>' not specified"
  if options.dryRun == options.experimentalSend then
    throw <| IO.userError "Choose exactly one invoice mode: --dry-run or --broadcast."
  if options.dryRun && options.journal.isSome then
    throw <| IO.userError "--journal is only valid with --broadcast."
  let chain ← match parseChainInput options.chain with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  if options.nonInteractive && options.keyFile.isNone then
    throw <| IO.userError "--non-interactive requires --key-file for deposits."
  let journal ← if options.experimentalSend then
      some <$> depositJournalPath options.journal chain
    else pure none
  let keyFile ← Tornado.Runtime.NativeSigner.resolveKeyFile options.keyFile journal
  if options.dryRun then
    Tornado.Cli.DepositSend.dryRunPayInvoice invoiceFile keyFile rpc chain
  else
    let some journal := journal
      | throw <| IO.userError "Deposit journal selection failed."
    Tornado.Cli.DepositSend.experimentalPayInvoice invoiceFile keyFile rpc journal chain false options.nonInteractive

private structure MultiDepositOptions where
  notesFile : Option String := none
  keyFile : Option String := none
  chain : String := "1"
  rpc : Option String := none
  sequential : Bool := false
  delegated : Bool := false
  resume : Bool := false
  dryRun : Bool := false
  experimentalSend : Bool := false
  nonInteractive : Bool := false
  journal : Option String := none
  bundler : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseMultiDepositOptions (args : List String)
    (options : MultiDepositOptions := {}) : Except String MultiDepositOptions :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--notes-file" :: value :: rest =>
      parseMultiDepositOptions rest { options with notesFile := some value }
  | "--key-file" :: value :: rest =>
      parseMultiDepositOptions rest { options with keyFile := some value }
  | "--chain" :: value :: rest =>
      parseMultiDepositOptions rest { options with chain := value }
  | "--rpc" :: value :: rest =>
      parseMultiDepositOptions rest { options with rpc := some value }
  | "--sequential" :: rest =>
      parseMultiDepositOptions rest { options with sequential := true }
  | "--delegated" :: rest =>
      parseMultiDepositOptions rest { options with delegated := true }
  | "--resume" :: rest =>
      parseMultiDepositOptions rest { options with resume := true }
  | "--dry-run" :: rest =>
      parseMultiDepositOptions rest { options with dryRun := true }
  | "--broadcast" :: rest =>
      parseMultiDepositOptions rest { options with experimentalSend := true }
  | "--non-interactive" :: rest =>
      parseMultiDepositOptions rest { options with nonInteractive := true }
  | "--journal" :: value :: rest =>
      parseMultiDepositOptions rest { options with journal := some value }
  | "--bundler-url" :: value :: rest =>
      parseMultiDepositOptions rest { options with bundler := some value }
  | ["--notes-file"] | ["--key-file"] | ["--chain"] | ["--rpc"] | ["--journal"] |
    ["--bundler-url"] =>
      .error "error: option argument missing"
  | value :: rest =>
      if value.startsWith "--notes-file=" then
        parseMultiDepositOptions rest { options with notesFile := some (String.ofList (value.toList.drop 13)) }
      else if value.startsWith "--key-file=" then
        parseMultiDepositOptions rest { options with keyFile := some (String.ofList (value.toList.drop 11)) }
      else if value.startsWith "--chain=" then
        parseMultiDepositOptions rest { options with chain := String.ofList (value.toList.drop 8) }
      else if value.startsWith "--rpc=" then
        parseMultiDepositOptions rest { options with rpc := some (String.ofList (value.toList.drop 6)) }
      else if value.startsWith "--journal=" then
        parseMultiDepositOptions rest { options with journal := some (String.ofList (value.toList.drop 10)) }
      else if value.startsWith "--bundler-url=" then
        parseMultiDepositOptions rest { options with bundler := some (String.ofList (value.toList.drop 14)) }
      else .error s!"error: unsupported deposit option '{value}'"

private def multiDepositHelp : String :=
  "Usage: tornado deposit send --notes-file <path> [--key-file <path>] [options]\n" ++
  "Deposit notes; choose --dry-run for review or --broadcast to send.\n" ++
  "One note defaults to ordinary transactions; --delegated explicitly selects a UserOperation.\n" ++
  "  --chain <id>       Ethereum chain ID (default: 1)\n" ++
  "  --key-file <path>  Optional; omit for hidden terminal entry (never stored as a key file)\n" ++
  "  --rpc <url>        HTTPS chain RPC URL\n" ++
  "  --sequential      Force ordinary transaction planning\n" ++
  "  --delegated       Force UserOperation deposits; authorize installing/replacing EOA delegation\n" ++
  "  --resume          Reconcile an existing sequential ETH journal and continue its unexposed suffix\n" ++
  "  --dry-run         Review without signing or submitting\n" ++
  "  --bundler-url <url>  Custom bundler for Simple7702 deposits\n" ++
  "  --journal <path>  Optional for new sends (unique file in current directory); required with --resume\n" ++
  "  --broadcast       Send reviewed transactions after typed approval\n" ++
  "  --non-interactive  Explicitly authorize sends/delegation without prompts; requires --key-file\n"

private def multiDepositCommand (args : List String) : IO String := do
  let options ← match parseMultiDepositOptions args with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  if options.help then return multiDepositHelp
  if options.sequential && options.delegated then
    throw <| IO.userError "--delegated and --sequential cannot be used together."
  if options.resume && options.delegated then
    throw <| IO.userError "--resume preserves the original sequential route and cannot use --delegated."
  if options.dryRun == options.experimentalSend then
    throw <| IO.userError "Choose exactly one deposit mode: --dry-run or --broadcast."
  if options.dryRun && options.journal.isSome && !options.resume then
    throw <| IO.userError "--journal is only valid with --broadcast."
  let some notesFile := options.notesFile
    | throw <| IO.userError "error: required option '--notes-file <path>' not specified"
  let chain ← match parseChainInput options.chain with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  if options.resume && options.journal.isNone then
    throw <| IO.userError "--resume requires the original --journal path."
  if options.nonInteractive && options.keyFile.isNone then
    throw <| IO.userError "--non-interactive requires --key-file for deposits."
  if !options.resume then
    if let some path := options.journal then
      if ← (System.FilePath.mk path).pathExists then
        throw <| IO.userError "Journal already exists. Keep it and rerun the same deposit send command with --resume."
  let journal ← if options.resume then pure options.journal
    else if options.experimentalSend then some <$> depositJournalPath options.journal chain
    else pure none
  let keyFile ← Tornado.Runtime.NativeSigner.resolveKeyFile options.keyFile journal
  if options.resume then
    return ← Tornado.Cli.DepositResume.command notesFile keyFile rpc journal.get! chain
      options.experimentalSend options.nonInteractive
  if options.experimentalSend then
    let some journal := journal
      | throw <| IO.userError "Deposit journal selection failed."
    let envBundler ← IO.getEnv "TORNADO_BUNDLER_URL"
    let selectedBundler := options.bundler.orElse (fun _ => envBundler)
    let bundler := selectedBundler.getD s!"https://public.pimlico.io/v2/{chainNumber chain}/rpc"
    return ← Tornado.Cli.DepositBatch7702.experimentalAutoSend notesFile keyFile rpc bundler
      journal chain options.sequential selectedBundler.isSome false options.delegated options.nonInteractive
  Tornado.Cli.DepositMulti.dryRun notesFile keyFile rpc chain options.sequential options.delegated

private structure FileOptions where
  file : Option String := none
  chain : String := "1"
  showHelp : Bool := false
  deriving Inhabited

private partial def parseFileOptions (args : List String)
    (options : FileOptions := {}) : Except String FileOptions :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--file" :: path :: rest => parseFileOptions rest { options with file := some path }
  | ["--file"] => .error "error: option '--file <path>' argument missing"
  | "--chain" :: chain :: rest => parseFileOptions rest { options with chain := chain }
  | ["--chain"] => .error "error: option '--chain <id>' argument missing"
  | argument :: rest =>
    if argument.startsWith "--file=" then
      parseFileOptions rest { options with file := some (String.ofList (argument.toList.drop 7)) }
    else if argument.startsWith "--chain=" then
      parseFileOptions rest { options with chain := String.ofList (argument.toList.drop 8) }
    else if argument.startsWith "-" then
      .error s!"error: unknown option '{argument}'"
    else .error "error: too many arguments"

private def fileHelp (command : String) : String :=
  s!"Usage: tornado notes {command} [options]\n\n" ++
  (if command == "inspect" then
    "Show public pool and commitment information without printing notes\n\n"
  else "Print Classic commitment-only invoices for a private backup\n\n") ++
  "Options:\n" ++
  "  --file <path>  Private note backup\n" ++
  "  --chain <id>   Ethereum chain ID (default: \"1\")\n" ++
  "  -h, --help     display help for command\n"

private def notesFileCommand (command : String) (args : List String) : IO String := do
  let options ← match parseFileOptions args with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  if options.showHelp then return fileHelp command
  let some path := options.file
    | throw <| IO.userError "error: required option '--file <path>' not specified"
  let chain ← match selectedChain options.chain with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk path).isAbsolute then path
    else (current / path).toString
  let bytes ← Tornado.Runtime.ProtectedIO.readPrivate absolute
  let some contents := String.fromUTF8? bytes
    | throw <| IO.userError "Private backup is not UTF-8."
  let found ← match parseDepositBackup contents chain with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let lines : List String ← if command == "inspect" then
      pure ((found.zipIdx).map fun (item, index) =>
        s!"{index + 1}. {item.note.pool.denomination} {item.note.pool.asset.symbol}\tpool {item.note.pool.address}\tcommitment {item.publicIdentity.commitment}")
    else
      found.mapM fun item => match invoiceForNote item.note.pool item.publicIdentity.commitment with
        | .ok value => pure value
        | .error error => throw <| IO.userError error
  return withLines lines

private partial def withdrawalStatusFileArg : List String → Option String
  | [] => none
  | "--status-file" :: value :: _ => some value
  | item :: rest =>
      if item.startsWith "--status-file=" then
        some (String.ofList (item.toList.drop 14))
      else withdrawalStatusFileArg rest

private def withdrawalStatusCommand (args : List String) : IO (String × UInt32) := do
  if args.contains "--help" || args.contains "-h" then
    return (← Tornado.Cli.WithdrawalStatusCommand.statusCommand args)
  let some file := withdrawalStatusFileArg args
    | return (← Tornado.Cli.WithdrawalStatusCommand.statusCommand args)
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let raw ← Tornado.Runtime.ProtectedIO.readPrivate absolute
  let some content := String.fromUTF8? raw
    | throw <| IO.userError "Withdrawal status file is not UTF-8."
  let kind ← match (Lean.Json.parse content).bind (·.getObjVal? "kind") with
    | .ok value => match value.getStr? with
      | .ok result => pure result
      | .error _ => throw <| IO.userError "Unsupported withdrawal status kind."
    | .error _ => throw <| IO.userError "Unsupported withdrawal status kind."
  if kind == "relayer" then
    Tornado.Cli.RelayerWithdrawalStatus.statusCommand args
  else if kind == "batch-4337" then
    Tornado.Cli.BatchWithdrawalStatus.statusCommand args
  else
    Tornado.Cli.WithdrawalStatusCommand.statusCommand args

def main (args : List String) : IO UInt32 := do
  if args == ["--version"] || args == ["-V"] then
    IO.println "0.1.0"
    return 0
  if args.isEmpty || args == ["--help"] || args == ["help"] then
    IO.print help
    return 0
  if args.take 2 == ["notes", "create"] || args.take 2 == ["notes", "create-plan"] then
    try
      let output ← if args[1]! == "create" then
        Tornado.Cli.NoteCreate.create (args.drop 2)
      else Tornado.Cli.NoteCreate.createPlan (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["notes", "inspect"] || args.take 2 == ["notes", "invoice"] then
    try
      let output ← notesFileCommand args[1]! (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["smart-account", "show"] then
    try
      let output ← Tornado.Cli.SmartAccountShow.showCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["smart-account", "status"] then
    try
      let (output, code) ← Tornado.Cli.SmartAccountStatus.statusCommand (args.drop 2)
      IO.print output
      return code
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["smart-account", "recover"] then
    try
      let output ← Tornado.Cli.RecoverySend.recoverCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["deposit", "pay-invoice"] then
    try
      let output ← payInvoiceCommand (args.drop 2)
      IO.println output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["deposit", "send"] then
    try
      let output ← multiDepositCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["deposit", "status"] then
    try
      let output ← Tornado.Cli.DepositStatusCommand.statusCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["withdraw", "status"] then
    try
      let (output, code) ← withdrawalStatusCommand (args.drop 2)
      IO.print output
      return code
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["withdraw", "one"] then
    try
      let (output, code) ← Tornado.Cli.SponsoredWithdraw.command false (args.drop 2)
      IO.print output
      return code
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["withdraw", "batch"] then
    try
      let (output, code) ← Tornado.Cli.SponsoredWithdraw.command true (args.drop 2)
      IO.print output
      return code
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["compliance", "report"] then
    try
      let output ← Tornado.Cli.History.complianceReportCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.head? == some "history" then
    try
      let output ← Tornado.Cli.History.historyCommand (args.drop 1)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  if args.take 2 == ["deposit", "inspect-status"] then
    try
      let output ← Tornado.Cli.DepositStatus.inspectCommand (args.drop 2)
      IO.print output
      return 0
    catch error =>
      let message := error.toString
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1
  match runReadOnly args with
  | .ok output =>
      IO.print output
      return 0
  | .error message =>
      IO.eprintln (if message.startsWith "error: " then message else s!"Error: {message}")
      return 1

end Tornado.Cli

def main (args : List String) : IO UInt32 := do
  try Tornado.Cli.main args
  finally Tornado.Runtime.NativeSigner.clearPromptKey
