import LeanCrypto.BIP32
import Tornado.Crypto.BIP39
import Tornado.Crypto.Constants

namespace Tornado.Crypto

export LeanCrypto (BIP32PrivateNode
  bip32MasterFromSeed
  bip32HardenedChild
  bip32HardenedPath
  BIP32PrivateNode.mk
  BIP32PrivateNode.rec
  BIP32PrivateNode.recOn
  BIP32PrivateNode.casesOn
  BIP32PrivateNode.privateKey
  BIP32PrivateNode.chainCode)

/-- The exact Tornado signature-v1 note key path for account index 0. -/
def tornadoNoteSigningKeyFromMnemonic (mnemonic : String) : Except String BIP32PrivateNode := do
  let seed ← mnemonicToSeedEnglish mnemonic
  let master ← bip32MasterFromSeed seed
  bip32HardenedPath master [29795, 1, 0]

end Tornado.Crypto
