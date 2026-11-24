import Tornado.Protocol.WitnessGraphCertificate
import Std.Data.HashSet.Lemmas

set_option autoImplicit false
namespace Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

abbrev PointRef := Nat × Nat

structure Footprint where
  kind : String
  inputs : Array Nat
  outputs : Array Nat
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable, Inhabited

abbrev Builder := StateT (Array Footprint) (Except String)

def operation (resolver : Resolver) (kind : String) (inputs : Array Nat) : Builder (Array Nat) := do
  let outputs ← compilePrimitive resolver kind inputs
  modify (·.push ⟨kind, inputs, outputs⟩)
  return outputs

def doubled (resolver : Resolver) (point : PointRef) : Builder PointRef := do
  let result ← operation resolver "MontgomeryDouble" #[point.1, point.2]
  return (result[2]!, result[3]!)

def added (resolver : Resolver) (first second : PointRef) : Builder PointRef := do
  let result ← operation resolver "MontgomeryAdd" #[first.1, first.2, second.1, second.2]
  return (result[1]!, result[2]!)

/-- Original note bytes are nullifier31 || secret31, little-endian within
each byte. The nullifier-only program takes the first248 bits. -/
def originalBit (resolver : Resolver) (commitment : Bool) (position : Nat) : Except String Nat := do
  if position >= (if commitment then 496 else 248) then throw "Pedersen reference bit is outside the note."
  let source := if position < 248 then 7 else 8
  let offset := if position < 248 then position else position - 248
  let input ← resolver.resolve (.input source)
  resolver.resolve (.bit input offset)

def window (resolver : Resolver) (commitment : Bool) (offset : Nat) (base : PointRef) : Builder (PointRef × PointRef) := do
  let twice ← doubled resolver base
  let mut table := #[base, twice]
  let mut previous := twice
  for _ in [2:8] do
    previous ← added resolver base previous
    table := table.push previous
  let b0 ← originalBit resolver commitment offset
  let b1 ← originalBit resolver commitment (offset + 1)
  let b2 ← originalBit resolver commitment (offset + 2)
  let sign ← originalBit resolver commitment (offset + 3)
  let inputs := #[b0, b1, b2] ++ table.map Prod.fst ++ table.map Prod.snd
  let mux ← operation resolver "MultiMux3" inputs
  let signed ← operation resolver "Window4" #[mux[18]!, sign]
  return ((mux[17]!, signed[0]!), previous)

/-- The independent window schedule uses magnitudes1..8 and weight32.
The two doubles after8*base advance the next window to32*base. -/
def segment (resolver : Resolver) (commitment : Bool) (offset windows : Nat) (base : PointRef) : Builder PointRef := do
  if windows == 0 then throw "Pedersen reference segment is empty."
  let converted ← operation resolver "Edwards2Montgomery" #[base.1, base.2]
  let mut nextBase := (converted[0]!, converted[1]!)
  let mut previousEight := nextBase
  let mut accumulator : Option PointRef := none
  for index in [0:windows] do
    if index != 0 then
      let sixteen ← doubled resolver previousEight
      nextBase ← doubled resolver sixteen
    let (selected, eight) ← window resolver commitment (offset + 4 * index) nextBase
    previousEight := eight
    accumulator ← match accumulator with
      | none => pure (some selected)
      | some previous => some <$> added resolver previous selected
  let some result := accumulator | throw "Pedersen reference has no segment result."
  let converted ← operation resolver "Montgomery2Edwards" #[result.1, result.2]
  return (converted[0]!, converted[1]!)

def babyAdded (resolver : Resolver) (first second : PointRef) : Builder PointRef := do
  let result ← operation resolver "BabyAdd" #[first.1, first.2, second.1, second.2]
  return (result[4]!, result[5]!)

structure Reference where
  commitment : PointRef
  nullifier : PointRef
  steps : Array Footprint

def referenceProgram (resolver : Resolver) (bases : Array PointRef) : Builder (PointRef × PointRef) := do
  if bases.size != 3 then throw "Pedersen reference requires three generators."
  let c0 ← segment resolver true 0 50 bases[0]!
  let c1 ← segment resolver true 200 50 bases[1]!
  let c2 ← segment resolver true 400 24 bases[2]!
  let first ← babyAdded resolver c0 c1
  let commitment ← babyAdded resolver first c2
  let n0 ← segment resolver false 0 50 bases[0]!
  let n1 ← segment resolver false 200 12 bases[1]!
  let nullifier ← babyAdded resolver n0 n1
  return (commitment, nullifier)

def referenceSchedule (resolver : Resolver) (graph : SelectedGraph) : Except String Reference := do
  if graph.bases.map BaseSeed.index != #[28551,28552,30747,30748,32867,32868,33871,33872,35967,35968] then
    throw "Pedersen reference base slots differ."
  let mut bases := #[]
  for index in [0:3] do
    let x ← resolver.resolve (.constant graph.bases[2*index]!.value)
    let y ← resolver.resolve (.constant graph.bases[2*index+1]!.value)
    bases := bases.push (x,y)
  let ((commitment,nullifier),steps) ← (referenceProgram resolver bases).run #[]
  return ⟨commitment,nullifier,steps⟩

def signalRoot (compiled : CompiledGraph) (index : Nat) : Except String Nat :=
  match compiled.signalRoots[index]? with
  | none => .error "Pedersen schedule signal is outside the compiled graph."
  | some root => .ok root

def outputRoot (compiled : CompiledGraph) (index : Nat) : Except String Nat := do
  if index == 49 then
    if compiled.commitmentAliases.size != 1 then throw "Pedersen commitment requires exactly one alias."
    let alias := compiled.commitmentAliases[0]!
    if alias.1 != (← signalRoot compiled 49) then throw "Pedersen commitment alias has the wrong original source."
    return alias.2
  signalRoot compiled index

def actualFootprint (compiled : CompiledGraph) (primitive : Primitive) : Except String Footprint := do
  if !primitive.shapeValid compiled.signalRoots.size then throw "Pedersen point primitive has invalid dimensions."
  return ⟨primitive.kind, ← primitive.inputs.mapM (signalRoot compiled), ← primitive.outputs.mapM (outputRoot compiled)⟩

def actualPointSteps (compiled : CompiledGraph) (graph : SelectedGraph) : Except String (Array Footprint) := do
  let mut steps := #[]
  for primitive in graph.primitives do
    if primitive.kind != "Square" then steps := steps.push (← actualFootprint compiled primitive)
  return steps

def footprintSetsMatch (expected actual : Array Footprint) : Bool :=
  let actualSet := Std.HashSet.ofList actual.toList
  let expectedSet := Std.HashSet.ofList expected.toList
  expected.all (fun step => actualSet.contains step) && actual.all (fun step => expectedSet.contains step)

def scheduleMatches (reference : Reference) (actual : Array Footprint) (compiled : CompiledGraph) : Bool :=
  footprintSetsMatch reference.steps actual && compiled.commitmentAliases.size == 1 &&
    (compiled.commitmentAliases[0]!).2 == reference.commitment.1 &&
    compiled.publicNullifier.2 == reference.nullifier.1 &&
    (compiled.commitmentAliases[0]!).1 == compiled.signalRoots[49]!

theorem footprintSetsMatch_sound (expected actual : Array Footprint)
    (checked : footprintSetsMatch expected actual = true) :
    (∀ step ∈ expected, step ∈ actual) ∧ (∀ step ∈ actual, step ∈ expected) := by
  have both := Bool.and_eq_true_iff.mp checked
  constructor
  · intro step member
    obtain ⟨index, bound, equal⟩ := Array.mem_iff_getElem.mp member
    rw [← equal]
    have contains := Array.all_eq_true.mp both.1 index bound
    rw [Std.HashSet.contains_ofList] at contains
    simpa only [Array.mem_toList_iff] using List.contains_iff_mem.mp contains
  · intro step member
    obtain ⟨index, bound, equal⟩ := Array.mem_iff_getElem.mp member
    rw [← equal]
    have contains := Array.all_eq_true.mp both.2 index bound
    rw [Std.HashSet.contains_ofList] at contains
    simpa only [Array.mem_toList_iff] using List.contains_iff_mem.mp contains

theorem scheduleMatches_sound (reference : Reference) (actual : Array Footprint) (compiled : CompiledGraph)
    (checked : scheduleMatches reference actual compiled = true) :
    (∀ step ∈ reference.steps, step ∈ actual) ∧ (∀ step ∈ actual, step ∈ reference.steps) ∧
      compiled.commitmentAliases.size = 1 ∧
      (compiled.commitmentAliases[0]!).2 = reference.commitment.1 ∧
      compiled.publicNullifier.2 = reference.nullifier.1 := by
  have strengthened := Bool.and_eq_true_iff.mp checked
  have last := Bool.and_eq_true_iff.mp strengthened.1
  have middle := Bool.and_eq_true_iff.mp last.1
  have first := Bool.and_eq_true_iff.mp middle.1
  have footprints := footprintSetsMatch_sound reference.steps actual first.1
  exact ⟨footprints.1, footprints.2, of_decide_eq_true first.2,
    of_decide_eq_true middle.2, of_decide_eq_true last.2⟩

/-- The names of source components are never used for admission. Every
point operation must have the expected kind, original bit/base roots and
all output roots; bidirectional membership admits structural sharing. -/
structure CertifiedSchedule (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph) : Type where
  private mk ::
  private accepted : ∃ reference actual,
    referenceSchedule resolver graph = .ok reference ∧ actualPointSteps compiled graph = .ok actual ∧
      scheduleMatches reference actual compiled = true

def certifySchedule (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph) :
    Except String (CertifiedSchedule resolver graph compiled) := do
  match expected : referenceSchedule resolver graph with
  | .error message => .error message
  | .ok reference =>
    match observed : actualPointSteps compiled graph with
    | .error message => .error message
    | .ok actual =>
      if checked : scheduleMatches reference actual compiled = true then
        .ok ⟨⟨reference,actual,expected,observed,checked⟩⟩
      else .error "Public point program differs from the independent Pedersen schedule."

theorem certifiedSchedule_accepted (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (certificate : CertifiedSchedule resolver graph compiled) :
    ∃ reference actual, referenceSchedule resolver graph = .ok reference ∧
      actualPointSteps compiled graph = .ok actual ∧ scheduleMatches reference actual compiled = true := certificate.accepted

theorem certifiedSchedule_intended (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (certificate : CertifiedSchedule resolver graph compiled) :
    ∃ reference actual, referenceSchedule resolver graph = .ok reference ∧
      actualPointSteps compiled graph = .ok actual ∧
      (∀ step ∈ reference.steps, step ∈ actual) ∧ (∀ step ∈ actual, step ∈ reference.steps) ∧
      compiled.commitmentAliases.size = 1 ∧ (compiled.commitmentAliases[0]!).2 = reference.commitment.1 ∧
      compiled.publicNullifier.2 = reference.nullifier.1 := by
  obtain ⟨reference, actual, expected, observed, checked⟩ := certificate.accepted
  obtain ⟨forward, reverse, count, commitment, nullifier⟩ := scheduleMatches_sound reference actual compiled checked
  exact ⟨reference,actual,expected,observed,forward,reverse,count,commitment,nullifier⟩

/-- The original commitment source is bound directly by public admission,
independently of whether a physical primitive declares output slot49. -/
theorem certifiedSchedule_alias_source (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (certificate : CertifiedSchedule resolver graph compiled) :
    (compiled.commitmentAliases[0]!).1 = compiled.signalRoots[49]! := by
  obtain ⟨_,_,_,_,checked⟩ := certificate.accepted
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2

end Tornado.Protocol.PedersenSchedule
#print axioms Tornado.Protocol.PedersenSchedule.certifiedSchedule_accepted
#print axioms Tornado.Protocol.PedersenSchedule.footprintSetsMatch_sound
#print axioms Tornado.Protocol.PedersenSchedule.scheduleMatches_sound
#print axioms Tornado.Protocol.PedersenSchedule.certifiedSchedule_intended

#print axioms Tornado.Protocol.PedersenSchedule.certifiedSchedule_alias_source
