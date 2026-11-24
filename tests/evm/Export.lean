import Lean
import Tornado.Protocol.AbiDecode
import Tornado.Protocol.SponsoredWithdrawal
import Tornado.Crypto.TornadoSignature

/-! Public local-EVM exports. The default mode exercises native ABI and
independent decoding with synthetic token-pool inputs. The `--builder` mode
invokes the actual SponsoredWithdrawal builder with a valid public proof. -/

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol

private def addressNat (text : String) : Except String Nat := do
  let bytes ← parseHexBytes text
  if bytes.size != 20 then throw "Expected a 20-byte synthetic local address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def hex (bytes : ByteArray) : Json := .str ("0x" ++ bytesToHex bytes)

private def generate (args : List String) : Except String Json := do
  let [ownerText, accountText, poolText, tokenText, recorderText, failText, receiverText, feeText] := args
    | throw "Expected eight synthetic local addresses."
  let owner ← addressNat ownerText
  let account ← addressNat accountText
  let pool ← addressNat poolText
  let token ← addressNat tokenText
  let recorder ← addressNat recorderText
  let failure ← addressNat failText
  let receiver ← addressNat receiverText
  let feeRecipient ← addressNat feeText
  let proof := ByteArray.mk #[0x12, 0x34]
  let root ← Abi.uintWord 11
  let nullifierHash ← Abi.uintWord 22
  let withdraw ← Abi.poolWithdraw proof root nullifierHash account feeRecipient 17 0
  let transfer ← Abi.erc20Transfer receiver 100
  let note11 := Abi.selector "note(uint256)" ++ (← Abi.uintWord 11)
  let note22 := Abi.selector "note(uint256)" ++ (← Abi.uintWord 22)
  let calls : Array Abi.ContractCall := #[
    { to := pool, value := 0, data := withdraw },
    { to := token, value := 0, data := transfer },
    { to := recorder, value := 0, data := note11 },
    { to := recorder, value := 0, data := note22 }]
  let batch ← Abi.accountExecuteBatchComposed calls
  if (← AbiDecode.decodeAccountExecuteBatch batch) != calls then
    throw "Independent native decoder disagrees with the emitted call list."
  let revertCalls : Array Abi.ContractCall := #[
    { to := recorder, value := 0, data := note11 },
    { to := failure, value := 0, data := Abi.selector "fail()" },
    { to := recorder, value := 0, data := note22 }]
  let revertBatch ← Abi.accountExecuteBatchComposed revertCalls
  let sponsor ← Abi.sponsorParameters {
    instanceAddress := pool, proof, root, nullifierHash := ← Abi.uintWord 33,
    recipient := account, fee := 17 }
  let factory ← Tornado.SmartAccount.accountFactoryData owner
  let decodedFactory ← AbiDecode.decodeFactoryCreate factory
  if decodedFactory.owner != owner then throw "Native factory owner did not decode."
  return Json.mkObj [
    ("scope", .str "native ABI encoders and independent decoders; synthetic pool proof"),
    ("batch", hex batch), ("revertBatch", hex revertBatch),
    ("tailBatch", hex (← Abi.accountExecuteBatchComposed (calls.extract 2 4))),
    ("withdraw", hex withdraw), ("transfer", hex transfer),
    ("sponsorParameters", hex sponsor), ("factoryData", hex factory),
    ("factorySalt", .str (toString decodedFactory.salt)),
    ("callCount", toJson calls.size), ("proof", hex proof),
    ("root", hex root), ("nullifierHash", hex nullifierHash)]

private def generateBuilder (args : List String) (fixture : Json) : Except String Json := do
  let [ownerText, recorderText] := args | throw "Expected owner and recorder addresses."
  let owner ← addressNat ownerText
  let recorder ← addressNat recorderText
  let account : SponsoredWithdrawal.Account := {
    address := 0x1000000000000000000000000000000000000001,
    owner, nonce := 0, deployed := true }
  let pool := 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let publicKey ← parseHexBytes "0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb"
  let note ← tornadoSignatureNote publicKey 1 0 pool
  let tree ← buildMimcTree #[note.commitment]
  let path ← mimcProofAt tree 0
  let request : ProverWorkerWire.Request := {
    chainId := 1, pool, commitment := note.commitment, nullifierHash := note.nullifierHash,
    leafIndex := path.index, root := path.root, siblings := path.siblings,
    pathIndices := path.pathIndices, recipient := account.address,
    relayer := ← SponsoredWithdrawal.paymaster 1, fee := 1, refund := 0 }
  let proof ← parseHexBytes (← (← fixture.getObjVal? "solidityProofHex").getStr?)
  let signals ← (← (← fixture.getObjVal? "publicSignals").getArr?).mapM fun raw => do
    let some number := (← raw.getStr?).toNat? | throw "Invalid proof fixture signal."
    return number
  let proven : SponsoredWithdrawal.NoteProof := {
    request, result := { requestHash := request.hash, proof, signals } }
  let tail : Array Abi.ContractCall := #[
    { to := recorder, value := 0, data := Abi.selector "note(uint256)" ++ (← Abi.uintWord 101) },
    { to := recorder, value := 0, data := Abi.selector "note(uint256)" ++ (← Abi.uintWord 202) }]
  let operation ← SponsoredWithdrawal.batch #[proven] account account.address tail {
    execution := 100000, maxFee := 1, priority := 1 }
  let decoded ← AbiDecode.decodeAccountExecuteBatch operation.callData
  if decoded != tail then throw "Actual builder output changed the reviewed tail."
  return Json.mkObj [
    ("scope", .str "actual SponsoredWithdrawal.batch; one public sponsor proof and two ordered tail calls"),
    ("callData", hex operation.callData), ("paymasterData", hex operation.paymasterData),
    ("proof", hex proof), ("root", hex (← Abi.uintWord request.root)),
    ("nullifierHash", hex (← Abi.uintWord request.nullifierHash)),
    ("account", .str "0x1000000000000000000000000000000000000001"),
    ("pool", .str "0x199112eb461ea7eec1d75b33343542e1d069b41c"),
    ("paymaster", .str "0xb0ffcdc890e969579d348f519a9c3920c2dd04a5"),
    ("denomination", .str "10000000000000000")]

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | "--builder" :: rest => do
      let raw ← IO.FS.readFile "fixtures/groth16-account-public-proof.json"
      pure (Json.parse raw >>= generateBuilder rest)
    | _ => pure (generate args)
  match result with
  | .error error => IO.eprintln error; return 1
  | .ok fixture => IO.println fixture.compress; return 0
