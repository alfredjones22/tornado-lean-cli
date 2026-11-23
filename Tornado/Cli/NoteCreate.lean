import Tornado.Domain.NoteCreation
import Tornado.Domain.ChainInput
import Tornado.Domain.Plan
import Tornado.Runtime.Entropy
import Tornado.Runtime.ProtectedIO

/-!
Native note-backup creation. This module samples each secret from the OS
CSPRNG, computes the note material in Lean, and writes it through the
exclusive private-file adapter. It never prints a note or seed phrase.
-/

namespace Tornado.Cli.NoteCreate

open Tornado.Domain

private structure Options where
  denom : Option String := none
  amount : Option String := none
  out : Option String := none
  asset : String := "ETH"
  chain : String := "1"
  count : String := "1"
  plan : String := "1"
  excluded : List String := []
  seedBundle : Bool := false
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--seed-bundle" :: rest => parseOptions rest { options with seedBundle := true }
  | "--denom" :: value :: rest => parseOptions rest { options with denom := some value }
  | "--amount" :: value :: rest => parseOptions rest { options with amount := some value }
  | "--out" :: value :: rest => parseOptions rest { options with out := some value }
  | "--asset" :: value :: rest => parseOptions rest { options with asset := value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--count" :: value :: rest => parseOptions rest { options with count := value }
  | "--plan" :: value :: rest => parseOptions rest { options with plan := value }
  | "--exclude" :: value :: rest =>
      let next := rest.takeWhile (fun item => !item.startsWith "-")
      parseOptions (rest.drop next.length)
        { options with excluded := options.excluded ++ (value :: next) }
  | ["--denom"] => .error "error: option '--denom <amount>' argument missing"
  | ["--amount"] => .error "error: option '--amount <amount>' argument missing"
  | ["--out"] => .error "error: option '--out <file>' argument missing"
  | ["--asset"] => .error "error: option '--asset <symbol>' argument missing"
  | ["--chain"] => .error "error: option '--chain <id>' argument missing"
  | ["--count"] => .error "error: option '--count <n>' argument missing"
  | ["--plan"] => .error "error: option '--plan <n>' argument missing"
  | ["--exclude"] => .error "error: option '--exclude <denominations...>' argument missing"
  | item :: rest =>
      if item.startsWith "--denom=" then
        parseOptions rest { options with denom := some (String.ofList (item.toList.drop 8)) }
      else if item.startsWith "--amount=" then
        parseOptions rest { options with amount := some (String.ofList (item.toList.drop 9)) }
      else if item.startsWith "--out=" then
        parseOptions rest { options with out := some (String.ofList (item.toList.drop 6)) }
      else if item.startsWith "--asset=" then
        parseOptions rest { options with asset := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--chain=" then
        parseOptions rest { options with chain := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--count=" then
        parseOptions rest { options with count := String.ofList (item.toList.drop 8) }
      else if item.startsWith "--plan=" then
        parseOptions rest { options with plan := String.ofList (item.toList.drop 7) }
      else if item.startsWith "--exclude=" then
        parseOptions rest { options with excluded := options.excluded ++
          [String.ofList (item.toList.drop 10)] }
      else if item.startsWith "-" then .error s!"error: unknown option '{item}'"
      else .error "error: too many arguments"

private def integer (raw name : String) (max : Nat := 100) : Except String Nat := do
  let some value := raw.toNat?
    | throw s!"{name} must be from 1 to {max}."
  if value == 0 || value > max then throw s!"{name} must be from 1 to {max}."
  return value

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

private def absolutePath (raw : String) : IO String := do
  let candidate := System.FilePath.mk raw
  if candidate.isAbsolute then return candidate.toString
  let current ← IO.currentDir
  return (current / candidate).toString

private def generate (pools : List Pool) (seedBundle : Bool) :
    IO (List CreatedNote × Option String) := do
  if seedBundle then
    let phrase ← fromExcept (Tornado.Crypto.entropyToMnemonicEnglish
      (← Tornado.Runtime.Entropy.readKernelRandom 32))
    let mut uuidEntropy := []
    for _ in pools do
      uuidEntropy := uuidEntropy ++ [← Tornado.Runtime.Entropy.readKernelRandom 16]
    let notes ← fromExcept (seededNotesFromMnemonic pools phrase uuidEntropy)
    return (notes, some phrase)
  let mut notes := []
  for pool in pools do
    let nullifierKey ← Tornado.Runtime.Entropy.readKernelRandom 32
    let saltKey ← Tornado.Runtime.Entropy.readKernelRandom 32
    let uuidEntropy ← Tornado.Runtime.Entropy.readKernelRandom 16
    notes := notes ++ [← fromExcept (independentNoteFromEntropy pool
      nullifierKey saltKey uuidEntropy)]
  return (notes, none)

private def backup (pools : List Pool) (out : String) (seedBundle : Bool) : IO String := do
  let (notes, phrase) ← generate pools seedBundle
  let contents ← fromExcept (formatDepositBackup notes phrase)
  let path ← absolutePath out
  Tornado.Runtime.ProtectedIO.createPrivate path contents.toUTF8
  return path

private def createHelp : String :=
  "Usage: tornado notes create [options]\n\n" ++
  "Create independent notes or one fresh 24-word seed session\n\n" ++
  "Options:\n" ++
  "  --denom <amount>  One supported denomination\n" ++
  "  --out <file>     New private backup file (mode 0600)\n" ++
  "  --asset <symbol> Asset symbol (default: \"ETH\")\n" ++
  "  --chain <id>     Ethereum chain ID (default: \"1\")\n" ++
  "  --count <n>      Number of notes (default: \"1\")\n" ++
  "  --seed-bundle    Fresh UI-compatible 24-word session\n" ++
  "  -h, --help       display help for command\n"

def create (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.showHelp then return createHelp
  let some denom := options.denom
    | throw <| IO.userError "error: required option '--denom <amount>' not specified"
  let some out := options.out
    | throw <| IO.userError "error: required option '--out <file>' not specified"
  let chain ← fromExcept (parseChainInput options.chain)
  let count ← fromExcept (integer options.count "Count")
  let some pool := poolFor chain denom options.asset
    | throw <| IO.userError "This denomination is unavailable in the pinned SDK paymaster catalog."
  let path ← backup (List.replicate count pool) out options.seedBundle
  return s!"Created {count} {pool.denomination} {pool.asset.symbol} note(s) in {path} (mode 0600).\n" ++
    "Back up this file before depositing. Anyone with its notes or seed phrase can withdraw the funds.\n"

private def createPlanHelp : String :=
  "Usage: tornado notes create-plan [options]\n\n" ++
  "Create a mixed-denomination backup from an exact amount plan\n\n" ++
  "Options:\n" ++
  "  --amount <amount>             Exact amount in asset units\n" ++
  "  --out <file>                  New private backup file (mode 0600)\n" ++
  "  --asset <symbol>              Asset symbol (default: \"ETH\")\n" ++
  "  --chain <id>                  Ethereum chain ID (default: \"1\")\n" ++
  "  --exclude <denominations...>  Exclude supported denominations from planning\n" ++
  "  --plan <n>                    1-based choice from deposit plan after the same exclusions (default: \"1\")\n" ++
  "  --seed-bundle                 Fresh UI-compatible 24-word session spanning all denominations\n" ++
  "  -h, --help                    display help for command\n"

def createPlan (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.showHelp then return createPlanHelp
  let some rawAmount := options.amount
    | throw <| IO.userError "error: required option '--amount <amount>' not specified"
  let some out := options.out
    | throw <| IO.userError "error: required option '--out <file>' not specified"
  let chain ← fromExcept (parseChainInput options.chain)
  let available := poolsFor chain (some options.asset)
  let some first := available.head?
    | throw <| IO.userError "This asset has no supported pools on the selected chain."
  let amount ← fromExcept (parseAmount rawAmount first.asset.decimals)
  let excluded ← fromExcept (parseExcludedDenominations options.excluded available)
  let allowed := available.filter (fun pool => !excluded.contains pool.amount)
  let choices ← fromExcept (denominationPlanChoices amount allowed)
  if choices.isEmpty then
    let _ ← fromExcept (requireDenominationPlan amount allowed)
    throw <| IO.userError "No exact Tornado packing is possible with these pool exclusions."
  let index ← fromExcept (integer options.plan "Plan choice" choices.length)
  let choice := choices[index - 1]!
  let _ ← fromExcept (validatePlan amount allowed choice)
  if choice.noteCount > 100 then
    throw <| IO.userError "This plan has more than 100 notes. Narrow the amount or allowed denominations."
  let pools := choice.entries.flatMap (fun entry => List.replicate entry.count entry.pool)
  let path ← backup pools out options.seedBundle
  let mode := if options.seedBundle then "seed-backed" else "independent"
  let lines := choice.entries.map fun entry =>
    s!"  {entry.count} × {entry.pool.denomination} {entry.pool.asset.symbol}"
  return s!"Created plan {index}: {choice.noteCount} {mode} notes totaling " ++
    s!"{formatUnitsExact amount first.asset.decimals} {first.asset.symbol}.\n" ++
    String.intercalate "\n" lines ++ "\n" ++
    s!"Private backup: {path} (mode 0600).\n" ++
    "Back up this file before depositing. Anyone with its notes or seed phrase can withdraw the funds.\n"

end Tornado.Cli.NoteCreate
