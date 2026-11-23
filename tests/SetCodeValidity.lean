import Tornado.Protocol.SetCodeValidity

open Tornado.Crypto
open Tornado.Protocol.Rlp
open Tornado.Protocol.TypedTransaction
open Tornado.Protocol.SetCodeValidity

private def require (condition : Bool) (label : String) : Except String Unit :=
  if condition then .ok () else .error s!"Set-code validity failure: {label}"

private def base : Transaction1559 :=
  { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1,
    maxFeePerGas := 2, gas := 46000,
    to := some 0x1111111111111111111111111111111111111111,
    value := 0 }

private def auth : Authorization7702 :=
  { chainId := 1, delegate := 0x2222222222222222222222222222222222222222,
    nonce := 0, signature := ⟨0, 1, 2⟩ }

private def tx : Transaction7702 :=
  { base, authorizations := #[auth] }

private def sig : Signature := ⟨0, 1, 2⟩

private def check : Except String Unit := do
  require (intrinsicGas7702 tx == 46000) "minimum one-authorization intrinsic gas"
  require ((validateSetCodeEnvelope tx sig).isOk) "valid envelope"
  require ((validateSetCodeIntent tx sig).isOk) "valid stateless intent"
  let strictBytes ← serializeSetCodeIntent tx sig
  let rawBytes ← serialize7702 tx (some sig)
  require (strictBytes == rawBytes) "strict serializer reuses exact raw bytes"

  let emptyAuth := { tx with authorizations := #[] }
  require ((serialize7702 emptyAuth (some sig)).isOk)
    "raw viem-compatible encoder accepts empty list"
  require (!(validateSetCodeEnvelope emptyAuth sig).isOk)
    "empty authorization list rejected"
  let createTx := { tx with base := { base with to := none } }
  require ((serialize7702 createTx (some sig)).isOk)
    "raw viem-compatible encoder accepts null destination"
  require (!(validateSetCodeEnvelope createTx sig).isOk)
    "null destination rejected"

  let underGas := { tx with base := { base with gas := 45999 } }
  require (!(validateSetCodeEnvelope underGas sig).isOk)
    "one wei of intrinsic gas shortfall rejected"
  let data := ByteArray.mk #[0x00, 0x01]
  let key := ByteArray.mk (Array.replicate 32 (0 : UInt8))
  let access : AccessEntry :=
    { address := 0x3333333333333333333333333333333333333333,
      storageKeys := #[key] }
  let costly := { tx with base :=
    { base with data, accessList := #[access], gas := 50320 } }
  require (intrinsicGas7702 costly == 50320)
    "EIP-2930 calldata and access costs plus EIP-7702 authorization cost"
  require ((validateSetCodeEnvelope costly sig).isOk)
    "exact complex intrinsic gas accepted"
  let costlyUnder := { costly with base := { costly.base with gas := 50319 } }
  require (!(validateSetCodeEnvelope costlyUnder sig).isOk)
    "complex intrinsic gas shortfall rejected"

  let widthOverflow := { tx with authorizations := #[{ auth with nonce := 2 ^ 64 }] }
  require (!(validateSetCodeEnvelope widthOverflow sig).isOk)
    "authorization nonce outside uint64 rejects envelope"
  let maxNonce := { tx with authorizations := #[{ auth with nonce := 2 ^ 64 - 1 }] }
  require ((validateSetCodeEnvelope maxNonce sig).isOk)
    "uint64 maximum nonce fits envelope"
  require (!(validateSetCodeIntent maxNonce sig).isOk)
    "uint64 maximum nonce would skip authorization"
  let beforeMax := { tx with authorizations := #[{ auth with nonce := 2 ^ 64 - 2 }] }
  require ((validateSetCodeIntent beforeMax sig).isOk)
    "last statelessly eligible authorization nonce"

  let outerHighS : Signature := { sig with s := secp256k1Order / 2 + 1 }
  require ((serialize7702 tx (some outerHighS)).isOk)
    "raw encoder accepts high-S signature bytes"
  require (!(validateSetCodeEnvelope tx outerHighS).isOk)
    "EIP-2 high-S outer signature rejected"
  let outerBoundary : Signature := { sig with s := secp256k1Order / 2 }
  require ((validateSetCodeEnvelope tx outerBoundary).isOk)
    "low-S inclusive boundary"
  let authHighS := { tx with authorizations :=
    #[{ auth with signature := { auth.signature with s := secp256k1Order / 2 + 1 } }] }
  require ((validateSetCodeEnvelope authHighS sig).isOk)
    "high-S authorization does not invalidate envelope"
  require (!(validateSetCodeIntent authHighS sig).isOk)
    "high-S authorization would be skipped"
  let authBoundary := { tx with authorizations :=
    #[{ auth with signature := { auth.signature with s := secp256k1Order / 2 } }] }
  require ((validateSetCodeIntent authBoundary sig).isOk)
    "low-S authorization inclusive boundary"

  let wrongChain := { tx with authorizations := #[{ auth with chainId := 2 }] }
  require ((validateSetCodeEnvelope wrongChain sig).isOk)
    "mismatched authorization chain does not invalidate envelope"
  require (!(validateSetCodeIntent wrongChain sig).isOk)
    "mismatched chain authorization would be skipped"
  let wildcard := { tx with authorizations := #[{ auth with chainId := 0 }] }
  require ((validateSetCodeIntent wildcard sig).isOk)
    "wildcard authorization chain ID is eligible"
  let revocation := { tx with authorizations := #[{ auth with delegate := 0 }] }
  require ((validateSetCodeIntent revocation sig).isOk)
    "zero delegate revocation is allowed by EIP-7702"
  let mixed := { tx with authorizations := #[auth, { auth with chainId := 2 }] }
  let mixedGas := { mixed with base := { base with gas := 71000 } }
  require (!(validateSetCodeIntent mixedGas sig).isOk)
    "every authorization must satisfy stateless intent checks"

  let badParity : Signature := { sig with yParity := 2 }
  require (!(validateSetCodeEnvelope tx badParity).isOk)
    "outer signature parity restricted to 0 or 1"
  let zeroR : Signature := { sig with r := 0 }
  require (!(validateSetCodeEnvelope tx zeroR).isOk)
    "zero outer signature scalar rejected"
  let noAuthSig := { tx with authorizations :=
    #[{ auth with signature := { auth.signature with s := 0 } }] }
  require (!(validateSetCodeEnvelope noAuthSig sig).isOk)
    "zero authorization signature scalar rejected by native raw guard"
  let badFee := { tx with base := { base with maxPriorityFeePerGas := 3 } }
  require (!(validateSetCodeEnvelope badFee sig).isOk)
    "base transaction fee ordering retained"
  let zeroChain := { tx with base := { base with chainId := 0 } }
  require (!(validateSetCodeEnvelope zeroChain sig).isOk)
    "base transaction chain ID retained"

  let publicTestKey := ByteArray.mk ((Array.replicate 31 (0 : UInt8)).push 1)
  let realAuth ← signAuthorization7702 1 auth.delegate 0 publicTestKey
  let realTx := { tx with authorizations := #[realAuth] }
  let realSigned ← sign7702 realTx publicTestKey
  require ((validateSetCodeIntent realTx realSigned.signature).isOk)
    "native low-S public-test signatures satisfy stateless intent gate"
  let strictSigned ← serializeSetCodeIntent realTx realSigned.signature
  require (strictSigned == realSigned.serialized)
    "strict bytes preserve native signed transaction exactly"

def main : IO Unit := do
  match check with
  | .ok () => IO.println "PASS: 34 EIP-7702 stateless envelope and intent checks"
  | .error message => throw (IO.userError message)
