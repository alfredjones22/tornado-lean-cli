import Tornado.Spec.BlindingBounds
import Tornado.Runtime.ProofBlinding

/-! Exhaustive finite reference checks and negative controls. All candidate
values are public synthetic integers; no entropy source or network is used. -/

open Tornado.Runtime.ProofBlinding Tornado.Spec.BlindingDistribution

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def streams (alphabet length : Nat) : List (List Nat) :=
  match length with
  | 0 => [[]]
  | n + 1 => (List.range alphabet).flatMap (fun x => (streams alphabet n).map (x :: ·))

/-- Independent reference: locate the first admissible prefix element and
pass only the unread suffix to the second sampler. -/
private def firstAccepted (q budget : Nat) (draws : List Nat) : Option (Nat × List Nat) := do
  let index ← (draws.take budget).findIdx? (fun value => admissible q value)
  let value ← draws[index]?
  return (value, draws.drop (index + 1))

private def referencePair (q budget : Nat) (draws : List Nat) : Option (Nat × Nat) := do
  let (r, rest) ← firstAccepted q budget draws
  let (s, _) ← firstAccepted q budget rest
  return (r, s)

def main : IO UInt32 := do
  let alphabet := 8
  let modulus := 5
  let budget := 2
  let singleStreams := streams alphabet budget
  let pairStreams := streams alphabet (budget + budget)
  require (singleStreams.length == 64 && pairStreams.length == 4096)
    "Finite entropy reference did not enumerate the complete alphabet product."
  for value in List.range 8 do
    let expected := (singleStreams.filter (fun xs =>
      (firstAccepted modulus budget xs).map (·.1) == some value)).length
    require (mass alphabet modulus budget (valueEvent value) == expected)
      "Operational sampler counts differ from exhaustive first-admissible reference."
    if 0 < value && value < modulus then
      require (expected == 12) "Valid scalar did not have its exact uniform count."
  require (mass alphabet modulus budget failureEvent == 16 &&
    mass alphabet modulus budget successEvent == 48 &&
    mass alphabet modulus budget (fun _ => 1) == 64)
    "Single normalization or explicit exhaustion mass changed."
  for r in List.range 6 do
    for s in List.range 6 do
      let expected := (pairStreams.filter (fun xs => referencePair modulus budget xs == some (r, s))).length
      require (pairMass alphabet modulus budget (pairValueEvent r s) == expected)
        "Sequential shared-loop counts differ from exhaustive next-unread-coordinate reference."
      if 0 < r && r < modulus && 0 < s && s < modulus then
        require (expected == 144) "Pair outputs are not exactly equiprobable."
  require (pairMass alphabet modulus budget successEvent == 2304 &&
    pairMass alphabet modulus budget failureEvent == 1792)
    "Pair success or exhaustion probability changed."
  require (mass alphabet modulus 0 failureEvent == 1 &&
    mass alphabet modulus 0 successEvent == 0)
    "Zero budget consumed an entropy coordinate."
  let modulo : DrawTree Nat := sampleLoop
    (.draw (fun value => .done (some (1 + value % 5)))) .abort 1
  require (DrawTree.count 8 1 modulo (valueEvent 1) == 2 &&
    DrawTree.count 8 1 modulo (valueEvent 5) == 1)
    "Modulo-reduction negative control failed to exhibit bias."
  let zeroAllowed : DrawTree Nat := sampleLoop
    (.draw (fun value => .done (if value < 5 then some value else none))) .abort 1
  require (DrawTree.count 8 1 zeroAllowed (valueEvent 0) == 1 &&
    mass 8 5 1 (valueEvent 0) == 0)
    "Zero-admission negative control was not distinguished from the runtime classifier."
  let reused : DrawTree (Nat × Nat) :=
    (sampler modulus budget).bind (fun r => .done (r, r))
  require (DrawTree.count alphabet (budget + budget) reused (pairValueEvent 1 2) == 0 &&
    pairMass alphabet modulus budget (pairValueEvent 1 2) == 144)
    "Reused-scalar negative control failed to exhibit pair dependence."
  IO.println "PASS: exhaustive sampler stream counts, normalization, sequential pair independence, and biased/reused-scalar negative controls"
  return 0
