import LeanCryptoProofs.GeneratorOrder
import LeanCryptoProofs.FrModel

set_option autoImplicit false

namespace LeanCrypto.Proofs.ScalarSubgroup

variable {G : Type*} [AddCommGroup G] {q : Nat}

theorem mod_nsmul (generator : G) (annihilates : q • generator = 0) (value : Nat) :
    (value % q) • generator = value • generator := by
  have split := congrArg (fun n => n • generator) (Nat.mod_add_div value q)
  dsimp only at split
  rw [add_nsmul, mul_nsmul, annihilates,
    nsmul_zero, add_zero] at split
  exact split

variable [NeZero q]

/-- A cyclic scalar-field action constructed from a proved q-torsion point.
No module structure on arbitrary curve points is assumed. -/
def scalarHom (generator : G) (annihilates : q • generator = 0) : ZMod q →+ G where
  toFun scalar := scalar.val • generator
  map_zero' := by simp
  map_add' first second := by
    rw [ZMod.val_add, mod_nsmul generator annihilates, add_nsmul]

theorem scalarHom_nat (generator : G) (annihilates : q • generator = 0) (value : Nat) :
    scalarHom generator annihilates (value : ZMod q) = value • generator := by
  change (value : ZMod q).val • generator = value • generator
  rw [ZMod.val_natCast, mod_nsmul generator annihilates]

theorem scalarHom_mul_nat (generator : G) (annihilates : q • generator = 0)
    (value : Nat) (scalar : ZMod q) :
    scalarHom generator annihilates ((value : ZMod q) * scalar) =
      value • scalarHom generator annihilates scalar := by
  rw [← nsmul_eq_mul, map_nsmul]

end LeanCrypto.Proofs.ScalarSubgroup

#print axioms LeanCrypto.Proofs.ScalarSubgroup.mod_nsmul
#print axioms LeanCrypto.Proofs.ScalarSubgroup.scalarHom_nat
#print axioms LeanCrypto.Proofs.ScalarSubgroup.scalarHom_mul_nat
