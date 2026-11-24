import TornadoProofs.Witness.Num2BitsRowProgram
import TornadoProofs.Witness.FeistelSupport
import TornadoProofs.Witness.Num2BitsSimulation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution

def bitFieldSum (bits : List Nat) (value : Nat) : Fr :=
  (bits.map (fun bit => model (2^bit) * model (bitValue value bit))).sum

theorem bitFieldSum_reconstruct (width value : Nat) (bound : value<2^width) :
    bitFieldSum (List.range width) value=model value := by
  have castSum (items : List Nat) : model items.sum=(items.map model).sum := by
    induction items with
    | nil => simp [model]
    | cons head rest ih => simp only [List.sum_cons,List.map_cons,model,Nat.cast_add] at *; rw [ih]
  have reconstructed := congrArg model (bitSum_reconstruct width value bound)
  rw [bitSum,castSum,List.map_map] at reconstructed
  simpa only [bitFieldSum,Function.comp_def,model,Nat.cast_mul] using reconstructed

theorem bitRows_forIn_sound (nodes : Array Node) (compiled : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index)=assignment index)
    (component : Num2BitsComponent) (value : Nat) (items : List Nat)
    (meaning : ∀ bit∈items, assignment component.outputs[bit]! = model (bitValue value bit))
    (initial output : BitRowsFrame) (valid : SystemSatisfied assignment initial.snd)
    (returned : forIn items initial (bitRowsEffect nodes compiled component)=.ok output) :
    SystemSatisfied assignment output.snd ∧
      linearValue assignment output.fst=linearValue assignment initial.fst+bitFieldSum items value := by
  induction items generalizing initial with
  | nil =>
    have equal : initial=output := Except.ok.inj returned
    subst output
    exact ⟨valid,by simp [bitFieldSum]⟩
  | cons bit rest ih =>
    have tail : forIn rest (bitRowsStep nodes compiled component bit initial)
        (bitRowsEffect nodes compiled component)=.ok output := by
      simpa only [List.forIn_cons,bitRowsEffect,bind,Except.bind,pure,Except.pure] using returned
    have row := rowValue component.outputs[bit]!
    have actual := meaning bit (by simp)
    have bitBoolean : model (bitValue value bit) * (model (bitValue value bit)-1)=0 := by
      have cases : bitValue value bit=0 ∨ bitValue value bit=1 := by
        have bound := bitValue_is_binary value bit
        omega
      rcases cases with equation | equation <;> simp [equation,model]
    have nextValid : SystemSatisfied assignment (bitRowsStep nodes compiled component bit initial).snd := by
      apply constraint_emit assignment constant _ _ _ _ valid
      simp only [minusLinear_value,row,constantLinear_value assignment constant]
      rw [actual]
      simpa only [show model 1=(1:Fr) from rfl,show linearValue assignment []=0 from rfl] using bitBoolean
    have tailMeaning : ∀ index∈rest, assignment component.outputs[index]! = model (bitValue value index) :=
      fun index member => meaning index (by simp only [List.mem_cons]; exact Or.inr member)
    obtain ⟨satisfied,accumulated⟩ := ih tailMeaning (bitRowsStep nodes compiled component bit initial) nextValid tail
    refine ⟨satisfied,?_⟩
    rw [accumulated]
    simp only [bitRowsStep,linear_add,linear_scale,row,actual,bitFieldSum,List.map_cons,List.sum_cons]
    ring

theorem num2BitsLocalSystem_sound (nodes : Array Node) (compiled : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index)=assignment index)
    (component : Num2BitsComponent) (value : Nat) (bound : value<2^component.outputs.size)
    (inputMeaning : assignment component.input=model value)
    (outputMeaning : ∀ bit,bit<component.outputs.size → assignment component.outputs[bit]! = model (bitValue value bit))
    (seed after : LocalSystem) (valid : SystemSatisfied assignment seed)
    (returned : num2BitsLocalSystem nodes compiled seed component=.ok after) :
    SystemSatisfied assignment after := by
  rw [num2BitsLocalSystem_source] at returned
  obtain ⟨frame,loop,finished⟩ := bind_success
    (forIn (List.range component.outputs.size) (⟨[],seed⟩ : BitRowsFrame) (bitRowsEffect nodes compiled component)) _ after returned
  have equal : frame.snd.linear (minusLinear (signalLinear nodes compiled component.input) frame.fst)=after := by
    simpa only [pure,Except.pure,Except.ok.injEq] using finished
  rw [←equal]
  have loopMeaning : ∀ bit∈List.range component.outputs.size,
      assignment component.outputs[bit]! = model (bitValue value bit) :=
    fun bit member => outputMeaning bit (List.mem_range.mp member)
  obtain ⟨frameValid,frameValue⟩ := bitRows_forIn_sound nodes compiled assignment constant rowValue component value
    (List.range component.outputs.size) loopMeaning (⟨[],seed⟩ : BitRowsFrame) frame valid loop
  apply linear_emit assignment frame.snd _ frameValid
  rw [minusLinear_value,rowValue,inputMeaning,frameValue]
  simp only [show linearValue assignment (MProd.fst (⟨[],seed⟩ : BitRowsFrame))=0 from rfl,zero_add]
  rw [bitFieldSum_reconstruct _ _ bound,sub_self]

/-- The original public bit compiler supplies the exact input and ordered
bit values satisfying its actual inline row generator. -/
theorem compileNum2Bits_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (state after : SignalState) (component : Num2BitsComponent)
    (sourceBound : ∀ input, state.read component.input=.ok input → values[input]! < 2^248)
    (compiled : compileNum2Bits resolver state component=.ok after)
    (aliases : AliasesValid after values) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (interpreted : SignalInterpretation after assignment values)
    (rowValue : ∀ index, linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (seed result : LocalSystem) (valid : SystemSatisfied assignment seed)
    (generated : num2BitsLocalSystem resolver.nodes compiledGraph seed component=.ok result) :
    SystemSatisfied assignment result := by
  obtain ⟨input,read⟩ := compileNum2Bits_read resolver state after component compiled
  have width := (compileNum2Bits_publicLoop resolver state after component input compiled read).1
  have bounded : values[input]! < 2^component.outputs.size := by
    simpa only [width] using sourceBound input read
  have executed := (compileNum2Bits_construct resolver inputs values denotes canonical state after component
    sourceBound compiled aliases).2
  rw [executeNum2Bits_eq_loop (realize state values) component values[input]!
    (signalRead_realize state values component.input input read) width bounded] at executed
  have post := runAssignments_success _ _ _ executed
  have original := read_assigned_of_success (realize state values) component.input values[input]!
    (signalRead_realize state values component.input input read)
  have inputMeaning := signalInterpretation_assigned after assignment values interpreted _ _
    (post.1.2 _ _ original)
  have outputMeaning (bit : Nat) (bound : bit<component.outputs.size) :
      assignment component.outputs[bit]! = model (bitValue values[input]! bit) := by
    have assigned := post.2 component.outputs[bit]! (bitValue values[input]! bit)
      (List.mem_map.mpr ⟨bit,List.mem_range.mpr bound,rfl⟩)
    exact signalInterpretation_assigned after assignment values interpreted _ _ assigned
  exact num2BitsLocalSystem_sound resolver.nodes compiledGraph assignment constant rowValue component values[input]!
    bounded inputMeaning outputMeaning seed result valid generated

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.bitFieldSum_reconstruct
#print axioms TornadoProofs.Witness.Local.bitRows_forIn_sound
#print axioms TornadoProofs.Witness.Local.num2BitsLocalSystem_sound
#print axioms TornadoProofs.Witness.Local.compileNum2Bits_localRows
