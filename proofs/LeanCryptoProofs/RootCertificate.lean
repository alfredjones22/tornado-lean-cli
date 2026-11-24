import LeanCrypto.Groth16.FFT

namespace LeanCrypto.Proofs.BN254Fr

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
theorem root_certificates :
    (List.range 17).all (fun log =>
      LeanCrypto.Groth16.FFT.validRoot (2 ^ log)
        (LeanCrypto.Groth16.FFT.powMod 7
          ((LeanCrypto.Groth16.FFT.modulus - 1) / (2 ^ log)))) = true := by
  decide +kernel

end LeanCrypto.Proofs.BN254Fr

#print axioms LeanCrypto.Proofs.BN254Fr.root_certificates
