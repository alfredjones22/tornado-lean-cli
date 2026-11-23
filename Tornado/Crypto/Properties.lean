import Tornado.Crypto.TornadoSignature

/-!
Kernel-checked input rejection properties of the native recovery path.
These prove that selected malformed inputs fail before key derivation or
signing. They do not establish SHA/Keccak/ECDSA/Pedersen correctness or
constant-time behavior; those require separate mathematical proofs.
-/

namespace Tornado.Crypto

theorem empty_entropy_cannot_make_mnemonic :
    (entropyToMnemonicEnglish ByteArray.empty).isOk = false := by decide

theorem empty_bip32_seed_rejected :
    (bip32MasterFromSeed ByteArray.empty).isOk = false := by decide

theorem empty_ecdsa_key_rejected :
    (secp256k1SignDigest ByteArray.empty ByteArray.empty).isOk = false := by decide

theorem every_non_32_byte_ecdsa_key_rejected
    (privateKey digest : ByteArray) (h : privateKey.size != 32) :
    (secp256k1SignDigest privateKey digest).isOk = false := by
  simp [secp256k1SignDigest, h]
  rfl

theorem zero_chain_id_rejected :
    (tornadoNoteTypedDataHash 0 0).isOk = false := by decide

theorem zero_chain_id_rejected_for_every_nonce (nonce : Nat) :
    (tornadoNoteTypedDataHash 0 nonce).isOk = false := by rfl

theorem nonce_over_uint64_rejected :
    (tornadoNoteTypedDataHash 1 (2 ^ 64)).isOk = false := by decide

theorem every_nonce_over_uint64_rejected (nonce : Nat) (h : nonce >= 2 ^ 64) :
    (tornadoNoteTypedDataHash 1 nonce).isOk = false := by
  simp [tornadoNoteTypedDataHash, h]
  rfl

theorem pool_address_over_uint160_rejected :
    (tornadoSignatureNote ByteArray.empty 1 0 (2 ^ 160)).isOk = false := by decide

theorem every_pool_address_over_uint160_rejected
    (privateKey : ByteArray) (chainId nonce poolAddress : Nat)
    (h : poolAddress >= 2 ^ 160) :
    (tornadoSignatureNote privateKey chainId nonce poolAddress).isOk = false := by
  simp [tornadoSignatureNote, h]
  rfl

end Tornado.Crypto

#print axioms Tornado.Crypto.empty_entropy_cannot_make_mnemonic
#print axioms Tornado.Crypto.empty_bip32_seed_rejected
#print axioms Tornado.Crypto.empty_ecdsa_key_rejected
#print axioms Tornado.Crypto.every_non_32_byte_ecdsa_key_rejected
#print axioms Tornado.Crypto.zero_chain_id_rejected
#print axioms Tornado.Crypto.zero_chain_id_rejected_for_every_nonce
#print axioms Tornado.Crypto.nonce_over_uint64_rejected
#print axioms Tornado.Crypto.every_nonce_over_uint64_rejected
#print axioms Tornado.Crypto.pool_address_over_uint160_rejected
#print axioms Tornado.Crypto.every_pool_address_over_uint160_rejected
