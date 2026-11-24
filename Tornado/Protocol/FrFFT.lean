import LeanCrypto.Groth16.FFT
import Tornado.Protocol.Groth16R1CS
import Tornado.Protocol.ProvingKey

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.FrFFT

export LeanCrypto.Groth16.FFT (modulus nqr maximumSize provingDomainSize add sub mul powMod inverse inverse_sound validSize validRoot rootOfUnity rootOfUnity_sound reverseBits fft ifft convolve sumEvaluations calculateH)

end Tornado.Protocol.FrFFT
