import TornadoProofs.Witness.Expressions

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution

theorem listMapM_ordered {A B : Type} (f : A → Except String B)
    (input : List A) (output : List B) (returned : input.mapM f = .ok output) :
    List.Forall₂ (fun a b => f a = .ok b) input output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at returned
    cases returned
    exact .nil
  | cons head tail ih =>
    cases first : f head with
    | error err => simp [List.mapM_cons,first,bind,Except.bind] at returned
    | ok value =>
      cases rest : tail.mapM f with
      | error err => simp [List.mapM_cons,first,rest,bind,Except.bind] at returned
      | ok values =>
        simp only [List.mapM_cons,first,rest,bind,Except.bind,pure,Except.pure,
          Except.ok.injEq] at returned
        cases returned
        exact .cons first (ih values rest)

theorem arrayMapM_ordered {A B : Type} (f : A → Except String B)
    (input : Array A) (output : Array B) (returned : input.mapM f = .ok output) :
    List.Forall₂ (fun a b => f a = .ok b) input.toList output.toList := by
  rw [Array.mapM_eq_mapM_toList] at returned
  cases mapped : input.toList.mapM f with
  | error err => simp [mapped] at returned
  | ok values =>
    simp only [mapped] at returned
    change Except.ok values.toArray = Except.ok output at returned
    cases returned
    exact listMapM_ordered f input.toList values mapped

theorem arrayMapM_size {A B : Type} (f : A → Except String B)
    (input : Array A) (output : Array B) (returned : input.mapM f = .ok output) :
    output.size = input.size := by
  have length := (arrayMapM_ordered f input output returned).length_eq
  simpa using length.symm

theorem arrayMapM_value {A B C : Type} (f : A → Except String B)
    (input : Array A) (output : Array B) (inputValue : A → C) (outputValue : B → C)
    (correct : ∀ a b, f a = .ok b → outputValue b = inputValue a)
    (returned : input.mapM f = .ok output) : output.map outputValue = input.map inputValue := by
  have ordered := arrayMapM_ordered f input output returned
  have mapper (left : List A) (right : List B)
      (ordered : List.Forall₂ (fun a b => f a = .ok b) left right) :
      right.map outputValue = left.map inputValue := by
    induction ordered with
    | nil => rfl
    | @cons a b input output found tail ih =>
      simp only [List.map_cons,correct a b found,ih]
  have equal := mapper _ _ ordered
  exact Array.toList_inj.mp (by simpa only [Array.toList_map] using equal)

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.listMapM_ordered
#print axioms TornadoProofs.Witness.Execution.arrayMapM_ordered
#print axioms TornadoProofs.Witness.Execution.arrayMapM_size
#print axioms TornadoProofs.Witness.Execution.arrayMapM_value
