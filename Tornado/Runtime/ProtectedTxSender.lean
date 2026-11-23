import Lean
import Tornado.Protocol.RpcReceipt
import Tornado.Protocol.TypedTransactionDecode
import Tornado.Runtime.HttpTransport

/-! One protected-key EIP-1559 transaction. A caller owns the durable journal
and exact call policy. The prepared callback must durably reserve the signed
hash before the first network exposure. Any later failure is unknown and
never causes a replacement signature or retry inside this engine. -/

namespace Tornado.Runtime.ProtectedTxSender

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol

structure Call where
  to : Nat
  data : ByteArray
  value : Nat
  label : String
  deriving Inhabited

structure Bounds where
  maxGas : Nat := 1000000
  maxGasCostWei : Nat := 20000000000000000
  valueGasDivisor : Nat := 10
  receiptPolls : Nat := 90
  receiptPollMs : UInt32 := 2000
  deriving Inhabited

structure Effects where
  rpc : Nat → JsonRpc.Method → Array Json → IO Json
  sign : Rlp.Transaction1559 → IO (Nat × TypedTransaction.SignedTyped)
  approve : String → IO Unit
  revalidate : IO Unit
  recordPrepared : Rlp.Transaction1559 → TypedTransaction.SignedTyped → IO Unit
  recordSubmitted : ByteArray → IO Unit
  recordConfirmed : RpcReceipt.Receipt → IO Unit
  validateReceipt : RpcReceipt.Receipt → IO Unit
  waitFinality : RpcReceipt.Receipt → IO Unit
  recordUnknown : ByteArray → IO Unit := fun _ => pure ()
  recordFailed : RpcReceipt.Receipt → IO Unit := fun _ => pure ()

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

def hex (value : ByteArray) : String := "0x" ++ bytesToHex value

def quantity (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

def address (value : Nat) : Except String String := do
  if value == 0 || value >= 2 ^ 160 then throw "Invalid transaction address."
  let word ← Abi.addressWord value
  return hex (word.extract 12 32)

private def rpcQuantity (value : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked value.getStr?)

private def field (value : Json) (name : String) : IO Json :=
  checked <| value.getObjVal? name

private def fieldQuantity (value : Json) (name : String) : IO Nat := do
  rpcQuantity (← field value name)

private def bytesField (value : Json) (name : String) (size : Nat) : IO ByteArray := do
  let raw ← checked <| (← field value name).getStr?
  if !raw.startsWith "0x" then throw <| IO.userError "Malformed transaction hex."
  let bytes ← checked <| parseHexBytes raw
  if bytes.size != size then throw <| IO.userError "Wrong transaction hex width."
  return bytes

private def addrField (value : Json) (name : String) : IO Nat := do
  let bytes ← bytesField value name 20
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def feeQuote (effects : Effects) : IO (Nat × Nat) := do
  let result ← effects.rpc 103 .feeHistory
    #[toJson ("0x1" : String), toJson ("latest" : String), toJson (#[50] : Array Nat)]
  let bases ← checked <| (← field result "baseFeePerGas").getArr?
  let rewards ← checked <| (← field result "reward").getArr?
  if bases.size != 2 || rewards.size != 1 then
    throw <| IO.userError "Invalid bounded EIP-1559 fee history."
  let reward ← checked <| rewards[0]!.getArr?
  if reward.size != 1 then throw <| IO.userError "Invalid priority fee percentile."
  let base ← rpcQuantity bases[1]!
  let priority ← rpcQuantity reward[0]!
  let maximum := 2 * base + priority
  if maximum == 0 || maximum >= 2 ^ 256 then
    throw <| IO.userError "Invalid maximum EIP-1559 fee."
  return (priority, maximum)

def signedMatches (tx : Rlp.Transaction1559)
    (signed : TypedTransaction.SignedTyped) : Except String Unit := do
  if signed.transactionHash != keccak256 signed.serialized ||
      signed.signingHash != (← Rlp.signingHash1559 tx) ||
      (← Rlp.serialize1559 tx (some signed.signature)) != signed.serialized then
    throw "Signature bytes differ from the reviewed transaction."
  let decoded ← TypedTransactionDecode.decode1559 signed.serialized
  if decoded.signature.isNone ||
      (← Rlp.serialize1559 decoded.tx decoded.signature) != signed.serialized then
    throw "Signed transaction is not canonical EIP-1559."

private def nonceAt (effects : Effects) (senderText tag : String) (id : Nat) : IO Nat := do
  rpcQuantity (← effects.rpc id .getTransactionCount #[toJson senderText, toJson tag])

def prepare (effects : Effects) (chainId sender : Nat) (call : Call)
    (bounds : Bounds := {}) : IO Rlp.Transaction1559 := do
  if chainId == 0 || chainId >= 2 ^ 64 || call.data.size > 1024 * 1024 ||
      call.value >= 2 ^ 256 || bounds.maxGas == 0 || bounds.maxGas > 30000000 ||
      bounds.maxGasCostWei == 0 || bounds.maxGasCostWei >= 2 ^ 256 ||
      bounds.receiptPolls == 0 || bounds.receiptPolls > 180 ||
      bounds.receiptPollMs > 10000 then
    throw <| IO.userError "Invalid transaction or response bounds."
  let senderText ← checked <| address sender
  let targetText ← checked <| address call.to
  if (← rpcQuantity (← effects.rpc 100 .chainId #[])) != chainId then
    throw <| IO.userError "Transaction RPC is on a different chain."
  let nonce ← nonceAt effects senderText "pending" 101
  if nonce != (← nonceAt effects senderText "latest" 102) then
    throw <| IO.userError "Sender has a pending transaction; refusing replacement."
  let request := Json.mkObj [("from", toJson senderText), ("to", toJson targetText),
    ("data", toJson (hex call.data)), ("value", toJson (quantity call.value))]
  let estimate ← rpcQuantity (← effects.rpc 104 .estimateGas #[request])
  let gas := estimate * 120 / 100 + 1
  if estimate == 0 || gas > bounds.maxGas then
    throw <| IO.userError "Gas estimate exceeds the selected transaction bound."
  let (priority, maximum) ← feeQuote effects
  let gasCost := gas * maximum
  if gasCost > bounds.maxGasCostWei ||
      (call.value > 0 && bounds.valueGasDivisor > 0 &&
        gasCost > call.value / bounds.valueGasDivisor) then
    throw <| IO.userError "Maximum transaction gas cost exceeds the reviewed bound."
  let balance ← rpcQuantity (← effects.rpc 105 .getBalance
    #[toJson senderText, toJson ("pending" : String)])
  if balance < call.value + gasCost then
    throw <| IO.userError "Sender lacks the transaction value plus maximum gas cost."
  let tx : Rlp.Transaction1559 :=
    { chainId, nonce, maxPriorityFeePerGas := priority,
      maxFeePerGas := maximum, gas := gas,
      to := some call.to, value := call.value, data := call.data }
  let _ ← checked <| Rlp.validateTransaction tx
  return tx

/-- The transaction index response must describe the same signed call and
the same receipt inclusion. It remains an RPC claim, not consensus proof. -/
private def checkIndexed (effects : Effects) (sender : Nat)
    (tx : Rlp.Transaction1559) (hash : ByteArray)
    (receipt : RpcReceipt.Receipt) : IO Unit := do
  let indexed ← effects.rpc 401 .getTransactionByHash #[toJson (hex hash)]
  if indexed == .null then throw <| IO.userError "Transaction is not indexed."
  let input ← checked <| (← field indexed "input").getStr?
  if !input.startsWith "0x" || input.utf8ByteSize > 2 * 1024 * 1024 + 2 then
    throw <| IO.userError "Indexed calldata is malformed or too large."
  let data ← checked <| parseHexBytes input
  if (← bytesField indexed "hash" 32) != hash ||
      (← addrField indexed "from") != sender ||
      tx.to != some (← addrField indexed "to") ||
      (← fieldQuantity indexed "chainId") != tx.chainId ||
      (← fieldQuantity indexed "type") != 2 ||
      (← fieldQuantity indexed "nonce") != tx.nonce ||
      (← fieldQuantity indexed "value") != tx.value ||
      (← fieldQuantity indexed "gas") != tx.gas ||
      (← fieldQuantity indexed "maxFeePerGas") != tx.maxFeePerGas ||
      (← fieldQuantity indexed "maxPriorityFeePerGas") != tx.maxPriorityFeePerGas ||
      data != tx.data ||
      (← bytesField indexed "blockHash" 32) != receipt.blockHash ||
      (← fieldQuantity indexed "blockNumber") != receipt.blockNumber ||
      (← fieldQuantity indexed "transactionIndex") != receipt.transactionIndex then
    throw <| IO.userError "Indexed transaction differs from the signed call or receipt."

private def awaitReceipt (effects : Effects) (hash : ByteArray)
    (bounds : Bounds) : IO RpcReceipt.Receipt := do
  for attempt in [0:bounds.receiptPolls] do
    let value ← effects.rpc (500 + attempt) .getTransactionReceipt #[toJson (hex hash)]
    if value != .null then return (← checked <| RpcReceipt.parseReceipt value hash)
    if attempt + 1 < bounds.receiptPolls then IO.sleep bounds.receiptPollMs
  throw <| IO.userError "Transaction receipt is still unknown."

def sendWith (effects : Effects) (chainId sender : Nat) (call : Call)
    (bounds : Bounds := {}) : IO ByteArray := do
  let tx ← prepare effects chainId sender call bounds
  effects.approve s!"{call.label}; target {← checked <| address call.to}; value {tx.value} wei; calldata {hex tx.data}; nonce {tx.nonce}; gas {tx.gas}; maximum gas cost {tx.gas * tx.maxFeePerGas} wei."
  effects.revalidate
  let senderText ← checked <| address sender
  if (← rpcQuantity (← effects.rpc 110 .chainId #[])) != chainId ||
      (← nonceAt effects senderText "pending" 111) != tx.nonce ||
      (← nonceAt effects senderText "latest" 112) != tx.nonce then
    throw <| IO.userError "Chain or sender nonce changed after approval."
  let (actualSender, signed) ← effects.sign tx
  if actualSender != sender then throw <| IO.userError "Key differs from the reviewed sender."
  let _ ← checked <| signedMatches tx signed
  effects.recordPrepared tx signed
  let reverted ← IO.mkRef false
  -- From this point onward the durable journal retains the signed hash even
  -- if the network, receipt validation, or a later journal write fails.
  try
    let returned ← effects.rpc 300 .sendRawTransaction #[toJson (hex signed.serialized)]
    let raw ← checked returned.getStr?
    if !raw.startsWith "0x" || (← checked <| parseHexBytes raw) != signed.transactionHash then
      throw <| IO.userError "RPC returned a different transaction hash."
    effects.recordSubmitted signed.transactionHash
    let receipt ← awaitReceipt effects signed.transactionHash bounds
    if receipt.origin != sender || receipt.to != tx.to then
      throw <| IO.userError "Receipt sender or target differs from the signed call."
    checkIndexed effects sender tx signed.transactionHash receipt
    if !receipt.success then
      effects.recordFailed receipt
      reverted.set true
      throw <| IO.userError "Transaction reverted."
    effects.validateReceipt receipt
    effects.waitFinality receipt
    effects.recordConfirmed receipt
    return signed.transactionHash
  catch _ =>
    if !(← reverted.get) then
      try effects.recordUnknown signed.transactionHash catch _ => pure ()
    throw <| IO.userError s!"Transaction outcome requires reconciliation for {hex signed.transactionHash}; no replacement was signed."

/-- Twelve-block receipt stability check used by live adapters. RPC truth
and eventual Ethereum finality remain caller assumptions. -/
def waitReceiptDepth (rpc : String) (original : RpcReceipt.Receipt) : IO Unit := do
  for attempt in [0:180] do
    let id := 8000 + attempt * 3
    let head ← rpcQuantity (← HttpTransport.call rpc id .blockNumber #[])
    if head >= original.blockNumber + 11 then
      let block ← HttpTransport.call rpc (id + 1) .getBlockByNumber
        #[toJson (quantity original.blockNumber), toJson false]
      if (← fieldQuantity block "number") != original.blockNumber ||
          (← bytesField block "hash" 32) != original.blockHash then
        throw <| IO.userError "Transaction block changed during confirmation wait."
      let latest ← checked <| RpcReceipt.parseReceipt
        (← HttpTransport.call rpc (id + 2) .getTransactionReceipt
          #[toJson (hex original.transactionHash)]) original.transactionHash
      if latest.blockHash != original.blockHash ||
          latest.blockNumber != original.blockNumber ||
          latest.transactionIndex != original.transactionIndex ||
          latest.origin != original.origin || latest.to != original.to ||
          latest.success != original.success then
        throw <| IO.userError "Transaction receipt changed during confirmation wait."
      return
    IO.sleep 2000
  throw <| IO.userError "Twelve confirmations were not observed."

end Tornado.Runtime.ProtectedTxSender
