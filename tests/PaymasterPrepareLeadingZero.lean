import Tornado.Cli.PaymasterPrepare

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.SponsoredWithdrawal
open Tornado.Cli.PaymasterPrepare

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (value : Json) (name : String) : IO Json :=
  checked <| value.getObjVal? name

private def text (value : Json) : IO String := checked value.getStr?

private def quantity (value : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← text value)

-- Public synthetic verifier code and addresses. The catalog pool with a
-- leading zero moves through every selected-note position; no RPC is used.
private def poolTexts : Array String := #[
  "0x0e999c5285141ccb6dfae68a0921f37abd3e6a87",
  "0x8c4a04d872a6c1be37964a21ba3a138525dff50b",
  "0x8cc930096b4df705a007c4a039bdfa1320ed2508"]

private def verifierTexts : Array String := #[
  "0x0011111111111111111111111111111111111111",
  "0x2222222222222222222222222222222222222222",
  "0x3333333333333333333333333333333333333333"]

private def shadowTexts : Array String := #[
  "0x00000000000000000000000000004b6f68616b75",
  "0x00000000000000000000000000004b6f68616b76",
  "0x00000000000000000000000000004b6f68616b77"]

private def codes : Array String := #["0x60006000", "0x60016000", "0x60026000"]

private def addressNat (value : String) : IO Nat := do
  let bytes ← checked <| parseHexBytes value
  require (bytes.size == 20) "Fixture address is not exactly20 bytes."
  return bytes.data.foldl (fun n b => n*256+b.toNat) 0

private def scenario (rotation : Nat) : IO Unit := do
  let orderedPools := (#[0,1,2] : Array Nat).map (fun index => poolTexts[(index+rotation)%3]!)
  let orderedVerifiers := (#[0,1,2] : Array Nat).map (fun index => verifierTexts[(index+rotation)%3]!)
  let orderedCodes := (#[0,1,2] : Array Nat).map (fun index => codes[(index+rotation)%3]!)
  let mut notes := #[]
  for index in [0:3] do
    notes := notes.push ({
      chainId := 11155111, pool := ← addressNat orderedPools[index]!, commitment := 42+index,
      nullifierHash := 52+index, leafIndex := 0, root := 44,
      siblings := Array.replicate 20 0, pathIndices := Array.replicate 20 0,
      recipient := 2, relayer := 0, fee := 0, refund := 0 } : Request)
  let input : Input := { notes, mode := .batch ⟨3,4,0,true⟩ 5 #[], checkedBlock := 100 }
  let reads ← IO.mkRef (0 : Nat)
  let codeReads ← IO.mkRef (0 : Nat)
  let estimates ← IO.mkRef (0 : Nat)
  let random ← IO.mkRef (1000 : Nat)
  let effects : Effects := {
    rpc := fun method params => do
      match method with
      | .chainId => return toJson ("0xaa36a7" : String)
      | .blockNumber => return toJson ("0x64" : String)
      | .feeHistory => return Json.mkObj [
          ("baseFeePerGas", toJson #["0x3b9aca00", "0x3b9aca00"]),
          ("reward", toJson #[#["0x3b9aca00"]])]
      | .getBlockByNumber => return Json.mkObj [("baseFeePerGas", toJson ("0x3b9aca00" : String))]
      | .maxPriorityFee => return toJson ("0x3b9aca00" : String)
      | .call =>
        let index ← reads.get
        require (index < 3) "Unexpected additional contract read."
        require ((← text (← field params[0]! "to")) == orderedPools[index]!)
          "Pool verifier query lost its fixed20-byte address."
        require ((← text (← field params[0]! "data")) == Bundler.dataHex (Abi.selector "verifier()"))
          "Unexpected public contract query."
        reads.modify (·+1)
        let value ← addressNat orderedVerifiers[index]!
        return toJson (Bundler.dataHex (← checked <| Abi.uintWord value))
      | .getCode =>
        let index ← codeReads.get
        require (index < 3) "Unexpected additional verifier code read."
        require ((← text params[0]!) == orderedVerifiers[index]!)
          "Verifier code query lost its leading zero or fixed20-byte width."
        codeReads.modify (·+1)
        return toJson orderedCodes[index]!
      | _ => throw <| IO.userError "Unexpected RPC in public leading-zero fixture."
    bundler := fun method _ => do
      require (method == .pimlicoGasPrice) "Fixture attempted a money-moving bundler method."
      return Json.mkObj [("standard", Json.mkObj [
        ("maxFeePerGas", toJson ("0xb2d05e00" : String)),
        ("maxPriorityFeePerGas", toJson ("0x3b9aca00" : String))])]
    estimate := fun params => do
      estimates.modify (·+1)
      require (params.size == 3 && (← reads.get) == 3 && (← codeReads.get) == 3)
        "Estimation omitted a selected verifier or its state overrides."
      require ((← text (← field params[0]! "signature")) == Bundler.dataHex (← checked dummySignature))
        "Estimation disclosed an owner signature."
      let sponsor ← checked <| Abi.decodeSponsorParameters
        (← checked <| parseHexBytes (← text (← field params[0]! "paymasterData")))
      require (sponsor.proof == (← checked dummyProof)) "Estimation disclosed a real proof."
      for index in [0:3] do
        let shadow := shadowTexts[index]!
        require ((← text (← field (← field params[2]! shadow) "code")) == orderedCodes[index]!)
          "Shadow override lost the exact verifier code or20-byte key."
        let forwarder := "0x3660006000376000600036600073" ++ (shadow.drop 2).toString ++
          "5afa50600160005260206000f3"
        require ((← text (← field (← field params[2]! orderedVerifiers[index]!) "code")) == forwarder)
          "Verifier override lost its leading zero or exact forwarding destination."
      let stable (name : String) : IO Json := do
        let value ← quantity (← field params[0]! name)
        return toJson (Bundler.quantity (value*10/12))
      return .estimated (Json.mkObj [
        ("verificationGasLimit", ← stable "verificationGasLimit"),
        ("callGasLimit", ← stable "callGasLimit"),
        ("preVerificationGas", ← stable "preVerificationGas"),
        ("paymasterVerificationGasLimit", ← stable "paymasterVerificationGasLimit"),
        ("paymasterPostOpGasLimit", ← stable "paymasterPostOpGasLimit")])
    randomField := do random.modify (·+1); random.get
    prove := fun _ => throw <| IO.userError "Public estimation requested a real proof."
    validateHistory := fun _ => pure () }
  let quote ← estimateWith effects input
  require (quote.requests.size == 3 && quote.estimation == .estimated && (← estimates.get) == 1)
    "Leading-zero Sepolia fixture did not complete bounded dummy estimation."

def main : IO UInt32 := do
  for rotation in [0:3] do scenario rotation
  IO.println "PASS: public Sepolia leading-zero pool/verifier/shadow addresses in all three batch positions; exact dummy-only overrides"
  return 0
