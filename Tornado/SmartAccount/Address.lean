import Tornado.Protocol.Abi
import Tornado.Domain.NoteIdentity

/-!
Local CREATE2 prediction for the pinned eth-infinitism v0.8 SimpleAccount
factory. The exact 680-byte ERC1967Proxy creation code is embedded in the
factory runtime whose hash the CLI already pins. The offline provenance and
reconstruction fixture is fixtures/smart-account-address-vectors.json.

This predicts the destination independently of an RPC's getAddress response.
It does not authenticate deployment, account state, or Ethereum consensus.
-/

namespace Tornado.SmartAccount.Address

open Tornado.Crypto Tornado.Domain Tornado.Protocol

def factory : Nat := 0x13e9ed32155810fdbd067d4522c492d6f68e5944
def implementation : Nat := 0x28426d752372d68d34340bd94390950dce3c9ec3
def senderCreator : Nat := 0x449ed7c3e6fee6a97311d4b55475df59c44add33

def withdrawalSalt : Nat :=
  (keccak256 "tornado-ui-new-era:withdrawal-account:v1".toUTF8).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0

def proxyCreationCodeHash : String :=
  "54c4f1416e8a5d49bacc9bbed20b8baa3e9e904e15b2000b9d3ea9d1ce6a4c94"

def proxyCreationCodeHex : String :=
  "0x60806040526102a88038038061001481610168565b92833981016040828203126101645781516001600160a01b03811692909190838303610164576020810151906001600160401b03821161016457019281601f8501121561016457835161006e610069826101a1565b610168565b9481865260208601936020838301011161016457815f926020809301865e86010152823b15610152577f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc80546001600160a01b031916821790557fbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b5f80a282511561013a575f8091610122945190845af43d15610132573d91610113610069846101a1565b9283523d5f602085013e6101bc565b505b604051608d908161021b8239f35b6060916101bc565b50505034156101245763b398979f60e01b5f5260045ffd5b634c9c8ce360e01b5f5260045260245ffd5b5f80fd5b6040519190601f01601f191682016001600160401b0381118382101761018d57604052565b634e487b7160e01b5f52604160045260245ffd5b6001600160401b03811161018d57601f01601f191660200190565b906101e057508051156101d157805190602001fd5b63d6bda27560e01b5f5260045ffd5b81511580610211575b6101f1575090565b639996b31560e01b5f9081526001600160a01b0391909116600452602490fd5b50803b156101e956fe60806040525f8073ffffffffffffffffffffffffffffffffffffffff7f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc5416368280378136915af43d5f803e156053573d5ff35b3d5ffdfea264697066735822122012ef914fc5c0fe0eff95047a7f10780a737a1ca4f30269b985bcf38a18e4d23464736f6c634300081c0033"

def proxyCreationCode : Except String ByteArray := do
  let bytes ← parseHexBytes proxyCreationCodeHex
  if bytes.size != 680 || bytesToHex (keccak256 bytes) != proxyCreationCodeHash then
    throw "Pinned smart-account proxy creation code is inconsistent."
  return bytes

/-- Constructor arguments are exactly address implementation and the dynamic
initialize(owner) calldata, using the original deployed factory's ABI. -/
def initCodeHash (owner : Nat) : Except String ByteArray := do
  if owner == 0 || owner >= Abi.maxAddress then
    throw "Enter a nonzero EOA owner address."
  let initialization := Abi.selector "initialize(address)" ++ (← Abi.addressWord owner)
  let constructor := (← Abi.addressWord implementation) ++ (← Abi.uintWord 64) ++
    (← Abi.dynamicBytes initialization)
  return keccak256 ((← proxyCreationCode) ++ constructor)

/-- Last twenty bytes of keccak256(0xff || factory || salt || initCodeHash).
No RPC-returned implementation, address or replacement creation code is used. -/
def predictWithSalt (owner salt : Nat) : Except String Nat := do
  if salt >= Abi.maxUint256 then throw "Smart-account salt exceeds uint256."
  let factoryBytes := ((← Abi.addressWord factory).extract 12 32)
  let digest := keccak256 (ByteArray.mk #[0xff] ++ factoryBytes ++
    (← Abi.uintWord salt) ++ (← initCodeHash owner))
  let predicted := (digest.extract 12 32).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0
  if predicted == 0 then throw "Predicted smart-account address is zero."
  return predicted

def predict (owner : Nat) : Except String Nat :=
  predictWithSalt owner withdrawalSalt

/-- A server may claim matching owner, slot and code values for any address.
The destination must first match the independent counterfactual prediction. -/
def validateReported (owner reportedImplementation reportedAccount : Nat) :
    Except String Unit := do
  if reportedImplementation != implementation then
    throw "The SimpleAccount implementation address differs from the pinned factory."
  if reportedAccount != (← predict owner) then
    throw "Smart-account address differs from the local pinned-factory prediction."

end Tornado.SmartAccount.Address

