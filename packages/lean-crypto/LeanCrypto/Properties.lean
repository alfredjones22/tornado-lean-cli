import LeanCrypto.BIP39
import LeanCrypto.BIP32
import LeanCrypto.Secp256k1

namespace LeanCrypto

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

end LeanCrypto

#print axioms LeanCrypto.empty_entropy_cannot_make_mnemonic
#print axioms LeanCrypto.empty_bip32_seed_rejected
#print axioms LeanCrypto.empty_ecdsa_key_rejected
#print axioms LeanCrypto.every_non_32_byte_ecdsa_key_rejected
