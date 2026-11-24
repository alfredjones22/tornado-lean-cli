import LeanCryptoProofs.SamplerField

open LeanCrypto.Sampling LeanCrypto.Probability.Rejection
open LeanCrypto.Proofs.SamplerField LeanCrypto.Proofs.BN254Fr

private def require (condition : Bool) (description : String) : IO Unit := do
  unless condition do throw <| IO.userError description

private def decodeField (bytes : ByteArray) : Except String (Option Nat) :=
  (admitCandidate bytes).map (fun value => value.map
    (fun scalar => (scalarFieldEquiv scalar).val.val))

private def sampleEvent (kind : Nat) : Option (Nat × Nat) → Nat
  | none => if kind % 2 == 0 then 1 else 0
  | some (r, s) => match kind with
    | 0 => 1
    | 1 => 0
    | 2 => if r == s then 1 else 0
    | 3 => if r % 2 == 1 && s % 2 == 0 then 1 else 0
    | 4 => if r + s < 5 then 1 else 0
    | 5 => if r == 0 || s == 0 then 1 else 0
    | 6 => if (r * s + 3 * r + s) % 7 == 1 then 1 else 0
    | _ => r + 2 * s

def main : IO Unit := do
  for value in #[1, 2, 17, 255, 256, Q - 1] do
    let some scalar := admitValue value
      | throw <| IO.userError "A canonical public scalar was rejected"
    require ((scalarFieldEquiv scalar).val.val == value)
      "Scalar-to-field representation changed a canonical value"
    require ((scalarFieldEquiv.symm (scalarFieldEquiv scalar)).value == value)
      "Scalar-field inverse changed a canonical value"
    let encoded := LeanCrypto.FixedBytes.encode 32 value
    match decodeField encoded with
    | .ok (some actual) => require (actual == value) "Byte-to-field admission changed the value"
    | _ => throw <| IO.userError "Byte-to-field admission rejected a canonical value"
  for value in #[0, Q, Q + 1, 2 ^ 256 - 1] do
    require ((admitValue value).isNone) "Canonical Nat admission accepted zero or an overflow"
    match decodeField (LeanCrypto.FixedBytes.encode 32 value) with
    | .ok none => pure ()
    | _ => throw <| IO.userError "Field-cast admission silently wrapped an invalid Nat"
  for width in #[0, 1, 31, 33] do
    require (!(decodeField (LeanCrypto.FixedBytes.encode width 1)).isOk)
      "Field-cast admission accepted malformed byte width"
  -- Exhaustive original draw-tree evaluation, compared with the proved
  -- arbitrary-event formula. Includes weighted events and failure events.
  for config in #[(1, 1), (3, 2), (4, 3), (8, 7)] do
    let (alphabet, modulus) := config
    for budget in [0:3] do
      for kind in [0:8] do
        let event := sampleEvent kind
        let actual := pairMass alphabet modulus budget event
        let expected := pairMass alphabet modulus budget failureEvent * event none +
          successWeight alphabet modulus budget ^ 2 * sumTo (modulus - 1) (fun i =>
            sumTo (modulus - 1) (fun j => event (some (i + 1, j + 1))))
        require (actual == expected) "Arbitrary-event sequential sampler count changed"
  let counted := pairMass 8 7 2 (sampleEvent 2)
  let wrongFieldCast := pairMass 8 7 2 (fun result => sampleEvent 2
    (result.map fun (r, s) => (r % 2, s % 2)))
  require (counted != wrongFieldCast) "Negative control failed to detect an incorrect scalar representation"
  IO.println "PASS: actual Scalar-field bijection and byte admission boundaries; arbitrary-event sequential counts, failure mass, and incorrect-cast negative control"
