import Tornado.Protocol.BN254Groth16Verify

/-!
The Classic six-public-signal verification key is compiled into this module.
The decimal coordinates come from the immutable, vendored Tornado Core
Verifier.sol snapshot named below. The offline provenance check compares all
of them with that source, and with the overlapping pinned proving-key points.
There is no runtime JSON-supplied verification key in `verifyClassic`.
This does not establish that a selected pool uses that deployed verifier.
-/

namespace Tornado.Protocol.ClassicVerifyingKey

def sourceCommit : String := "1ef6a263ac6a0e476d063fcb269a9df65a1bd56a"
def sourceSha256 : String :=
  "a2fd9a12dc008ae95e1f9da2968e7d017617e804f22aa0491d2e8a91d965a824"

private def g1 (x y : Nat) : Except String Tornado.Protocol.BN254G1.Affine :=
  Tornado.Protocol.BN254G1.Affine.checked x y

private def g2 (x0 x1 y0 y1 : Nat) : Except String Tornado.Protocol.BN254G2.Affine :=
  Tornado.Protocol.BN254G2.Affine.checked x0 x1 y0 y1

/-- The complete pinned key is checked for canonical field coordinates and
    curve/twist membership before it can be returned. G2 subgroup membership
    is checked by the pairing implementation when `verifyClassic` runs. -/
def checkedKey : Except String Tornado.Protocol.BN254Groth16Verify.VerifyingKey := do
  let alpha1 ← g1
    20692898189092739278193869274495556617788530808486270118371701516666252877969
    11713062878292653967971378194351968039596396853904572879488166084231740557279
  let beta2 ← g2
    281120578337195720357474965979947690431622127986816839208576358024608803542
    12168528810181263706895252315640534818222943348193302139358377162645029937006
    9011703453772030375124466642203641636825223906145908770308724549646909480510
    16129176515713072042442734839012966563817890688785805090011011570989315559913
  let gamma2 ← g2
    10857046999023057135944570762232829481370756359578518086990519993285655852781
    11559732032986387107991004021392285783925812861821192530917403151452391805634
    8495653923123431417604973247489272438418190587263600148770280649306958101930
    4082367875863433681332203403145435568316851327593401208105741076214120093531
  let delta2 ← g2
    150879136433974552800030963899771162647715069685890547489132178314736470662
    21280594949518992153305586783242820682644996932183186320680800072133486887432
    11434086686358152335540554643130007307617078324975981257823476472104616196090
    1081836006956609894549771334721413187913047383331561601606260283167615953295
  let ic ← (#[(
    16225148364316337376768119297456868908427925829817748684139175309620217098814,
    5167268689450204162046084442581051565997733233062478317813755636162413164690), (
    12882377842072682264979317445365303375159828272423495088911985689463022094260,
    19488215856665173565526758360510125932214252767275816329232454875804474844786), (
    13083492661683431044045992285476184182144099829507350352128615182516530014777,
    602051281796153692392523702676782023472744522032670801091617246498551238913), (
    9732465972180335629969421513785602934706096902316483580882842789662669212890,
    2776526698606888434074200384264824461688198384989521091253289776235602495678), (
    8586364274534577154894611080234048648883781955345622578531233113180532234842,
    21276134929883121123323359450658320820075698490666870487450985603988214349407), (
    4910628533171597675018724709631788948355422829499855033965018665300386637884,
    20532468890024084510431799098097081600480376127870299142189696620752500664302), (
    15335858102289947642505450692012116222827233918185150176888641903531542034017,
    5311597067667671581646709998171703828965875677637292315055030353779531404812)] :
    Array (Nat × Nat)).mapM (fun point => g1 point.1 point.2)
  if ic.size != 7 then
    throw "Classic verifier key does not contain seven public-input points."
  return { alpha1, beta2, gamma2, delta2, ic }

/-- Verification using only the compiled-in Classic key. A malformed static
    point prevents verification rather than silently wrapping modulo Fp. -/
def verifyClassic (proof : Tornado.Protocol.BN254Groth16Verify.Proof)
    (signals : Array Nat) : Except String Bool :=
  if signals.size != 6 then .error "Classic verifier requires exactly six public signals."
  else match checkedKey with
    | .error message => .error message
    | .ok key => Tornado.Protocol.BN254Groth16Verify.verify key proof signals

/-- An accepted result necessarily used the statically checked key; the
    caller cannot replace it through this API. -/
theorem verifyClassic_true_uses_checked_key
    (proof : Tornado.Protocol.BN254Groth16Verify.Proof)
    (signals : Array Nat) (h : verifyClassic proof signals = .ok true) :
    ∃ key, checkedKey = .ok key ∧
      Tornado.Protocol.BN254Groth16Verify.verify key proof signals = .ok true := by
  by_cases six : signals.size = 6
  · cases hk : checkedKey with
    | error _ => simp [verifyClassic, six, hk] at h
    | ok key => exact ⟨key, rfl, by simpa [verifyClassic, six, hk] using h⟩
  · simp [verifyClassic, six] at h

theorem verifyClassic_rejects_wrong_dimensions
    (proof : Tornado.Protocol.BN254Groth16Verify.Proof) (signals : Array Nat)
    (wrong : signals.size ≠ 6) :
    verifyClassic proof signals = .error "Classic verifier requires exactly six public signals." := by
  simp [verifyClassic, wrong]

/-- The pinned-key wrapper inherits the native verifier's canonical Fr
    public-signal gate. This is not a Groth16 soundness theorem. -/
theorem verifyClassic_true_signals_bounded
    (proof : Tornado.Protocol.BN254Groth16Verify.Proof)
    (signals : Array Nat) (h : verifyClassic proof signals = .ok true) :
    signals.all (· < Tornado.Protocol.BN254G1.scalarPrime) = true := by
  obtain ⟨key, _, hv⟩ := verifyClassic_true_uses_checked_key proof signals h
  exact Tornado.Protocol.BN254Groth16Verify.verify_true_signals_bounded key proof signals hv

/-- The exact compiled coordinates are accepted, and the decoded key has
seven IC points. This is a closed kernel computation over public constants. -/
theorem checkedKey_accepted_seven :
    (checkedKey.toOption.map (fun key => key.ic.size)) = some 7 := by decide +kernel

theorem checkedKey_success_seven (key : Tornado.Protocol.BN254Groth16Verify.VerifyingKey)
    (accepted : checkedKey = .ok key) : key.ic.size = 7 := by
  have checked := checkedKey_accepted_seven
  simpa [accepted, Except.toOption] using checked

/-- The Classic wrapper retains its exact circuit dimensions even though the
standalone Groth16 verifier supports independently supplied dimensions. -/
theorem verifyClassic_true_dimensions (proof : Tornado.Protocol.BN254Groth16Verify.Proof)
    (signals : Array Nat) (accepted : verifyClassic proof signals = .ok true) :
    signals.size = 6 ∧
    ∃ key, checkedKey = .ok key ∧ key.ic.size = 7 ∧
      Tornado.Protocol.BN254Groth16Verify.verify key proof signals = .ok true := by
  have six : signals.size = 6 := by
    by_cases correct : signals.size = 6
    · exact correct
    · simp [verifyClassic, correct] at accepted
  obtain ⟨key, checked, verified⟩ := verifyClassic_true_uses_checked_key proof signals accepted
  exact ⟨six, key, checked, checkedKey_success_seven key checked, verified⟩

end Tornado.Protocol.ClassicVerifyingKey

#print axioms Tornado.Protocol.ClassicVerifyingKey.verifyClassic_true_uses_checked_key
#print axioms Tornado.Protocol.ClassicVerifyingKey.verifyClassic_true_signals_bounded

#print axioms Tornado.Protocol.ClassicVerifyingKey.checkedKey_accepted_seven
#print axioms Tornado.Protocol.ClassicVerifyingKey.checkedKey_success_seven
#print axioms Tornado.Protocol.ClassicVerifyingKey.verifyClassic_true_dimensions

#print axioms Tornado.Protocol.ClassicVerifyingKey.verifyClassic_rejects_wrong_dimensions
