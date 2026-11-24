import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace LeanCrypto.Proofs.MillerAlgebra

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Additive presentation of a symmetric normalized multiplicative
line-factor cocycle after final exponentiation. -/
structure Cocycle (A B : Type*) [AddCommGroup A] [AddCommGroup B] where
  value : A → A → B
  zeroLeft : ∀ x, value 0 x = 0
  symmetric : ∀ x y, value x y = value y x
  associative : ∀ x y z, value x y + value (x + y) z = value y z + value x (y + z)

theorem Cocycle.zeroRight (cocycle : Cocycle A B) (x : A) : cocycle.value x 0 = 0 := by
  rw [cocycle.symmetric, cocycle.zeroLeft]

theorem Cocycle.fourpoint (cocycle : Cocycle A B) (a b c d : A) :
    cocycle.value a b + cocycle.value (a + b) (c + d) + cocycle.value c d =
      cocycle.value a c + cocycle.value b d + cocycle.value (a + c) (b + d) := by
  have first := cocycle.associative a b (c + d)
  have second := cocycle.associative b c d
  have third := cocycle.associative a c (b + d)
  have fourth := cocycle.associative c b d
  rw [show c + (b + d) = b + (c + d) by abel] at third
  rw [show c + b = b + c by abel, cocycle.symmetric c b] at fourth
  calc
    _ = cocycle.value a (b + (c + d)) +
        (cocycle.value c d + cocycle.value b (c + d)) := by rw [first]; abel
    _ = cocycle.value a (b + (c + d)) +
        (cocycle.value b c + cocycle.value (b + c) d) := by rw [← second]
    _ = cocycle.value a (b + (c + d)) +
        (cocycle.value b d + cocycle.value c (b + d)) := by rw [fourth]
    _ = cocycle.value b d +
        (cocycle.value c (b + d) + cocycle.value a (b + (c + d))) := by abel
    _ = _ := by rw [← third]; abel

def miller (cocycle : Cocycle A B) : Nat → A → B
  | 0, _ => 0
  | n + 1, point => miller cocycle n point + cocycle.value (n • point) point

/-- The complete scalar-addition law, before invoking torsion. No Miller
success, pairing equality or bilinearity is assumed. -/
theorem miller_add (cocycle : Cocycle A B) (n : Nat) (first second : A) :
    miller cocycle n (first + second) + n • cocycle.value first second =
      miller cocycle n first + miller cocycle n second +
        cocycle.value (n • first) (n • second) := by
  induction n with
  | zero => simp only [miller, zero_nsmul, cocycle.zeroLeft, add_zero]
  | succ n ih =>
    have shuffle := cocycle.fourpoint (n • first) (n • second) first second
    rw [show n • first + n • second = n • (first + second) by rw [nsmul_add],
      show n • first + first = (n + 1) • first by rw [add_nsmul, one_nsmul],
      show n • second + second = (n + 1) • second by rw [add_nsmul, one_nsmul]] at shuffle
    simp only [miller, add_nsmul, one_nsmul]
    calc
      _ = (miller cocycle n (first + second) + n • cocycle.value first second) +
          (cocycle.value (n • (first + second)) (first + second) + cocycle.value first second) := by abel
      _ = (miller cocycle n first + miller cocycle n second) +
          (cocycle.value (n • first) (n • second) +
            cocycle.value (n • (first + second)) (first + second) + cocycle.value first second) := by rw [ih]; abel
      _ = (miller cocycle n first + miller cocycle n second) +
          (cocycle.value (n • first) first + cocycle.value (n • second) second +
            cocycle.value ((n + 1) • first) ((n + 1) • second)) := by rw [shuffle]
      _ = _ := by simp only [add_nsmul, one_nsmul]; abel

/-- Reduction kills the q-th coboundary term, so q-fold Miller evaluation
is additive on q-torsion inputs. -/
theorem miller_q_add (cocycle : Cocycle A B) (q : Nat) (first second : A)
    (firstTorsion : q • first = 0) (secondTorsion : q • second = 0)
    (factorTorsion : q • cocycle.value first second = 0) :
    miller cocycle q (first + second) = miller cocycle q first + miller cocycle q second := by
  have equation := miller_add cocycle q first second
  rw [firstTorsion, secondTorsion, factorTorsion, cocycle.zeroLeft, add_zero, add_zero] at equation
  exact equation

theorem miller_zero (cocycle : Cocycle A B) (n : Nat) : miller cocycle n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [miller, nsmul_zero, cocycle.zeroLeft, ih, add_zero]

/-- Scalar-sum identity gives both binary doubling and add-one recurrences
used by the original native Miller bit loop. -/
theorem miller_nat_add (cocycle : Cocycle A B) (n m : Nat) (point : A) :
    miller cocycle (n + m) point = miller cocycle n point + miller cocycle m point +
      cocycle.value (n • point) (m • point) := by
  induction m with
  | zero => simp only [miller, zero_nsmul, cocycle.zeroRight, add_zero]
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by omega, miller, ih]
    have identity := cocycle.associative (n • point) (m • point) point
    rw [← add_nsmul, show m • point + point = (m + 1) • point by rw [add_nsmul, one_nsmul]] at identity
    calc
      _ = miller cocycle n point + miller cocycle m point +
          (cocycle.value (n • point) (m • point) + cocycle.value ((n + m) • point) point) := by abel
      _ = miller cocycle n point + miller cocycle m point +
          (cocycle.value (m • point) point + cocycle.value (n • point) ((m + 1) • point)) := by rw [identity]
      _ = _ := by rw [miller]; abel

/-- A line-intersection reciprocity identity is a coboundary. Its complete
Miller sum telescopes without assuming general Weil reciprocity. -/
theorem miller_three_coboundary (first second third : Cocycle A B) (phi : A → B)
    (phiZero : phi 0 = 0)
    (reciprocity : ∀ x y, first.value x y + second.value x y + third.value x y =
      phi x + phi y - phi (x + y)) (n : Nat) (point : A) :
    miller first n point + miller second n point + miller third n point =
      n • phi point - phi (n • point) := by
  induction n with
  | zero => simp only [miller, zero_nsmul, phiZero, add_zero, sub_zero]
  | succ n ih =>
    simp only [miller]
    calc
      _ = (miller first n point + miller second n point + miller third n point) +
          (first.value (n • point) point + second.value (n • point) point + third.value (n • point) point) := by abel
      _ = (n • phi point - phi (n • point)) +
          (phi (n • point) + phi point - phi (n • point + point)) := by rw [ih, reciprocity]
      _ = _ := by simp only [add_nsmul, one_nsmul]; abel

theorem miller_three_coboundary_q (first second third : Cocycle A B) (phi : A → B)
    (phiZero : phi 0 = 0)
    (reciprocity : ∀ x y, first.value x y + second.value x y + third.value x y =
      phi x + phi y - phi (x + y)) (q : Nat) (point : A)
    (pointTorsion : q • point = 0) (outputTorsion : q • phi point = 0) :
    miller first q point + miller second q point + miller third q point = 0 := by
  rw [miller_three_coboundary first second third phi phiZero reciprocity q point,
    pointTorsion, outputTorsion, phiZero, sub_self]

/-- No nondegeneracy or reciprocity statement is hidden in this homomorphism
constructor; those are separate geometric obligations for native line factors. -/
def millerHom (cocycle : Cocycle A B) (q : Nat)
    (inputTorsion : ∀ point : A, q • point = 0)
    (factorTorsion : ∀ first second : A, q • cocycle.value first second = 0) : A →+ B where
  toFun := miller cocycle q
  map_zero' := miller_zero cocycle q
  map_add' := fun first second => miller_q_add cocycle q first second
    (inputTorsion first) (inputTorsion second) (factorTorsion first second)

end LeanCrypto.Proofs.MillerAlgebra

#print axioms LeanCrypto.Proofs.MillerAlgebra.Cocycle.zeroRight
#print axioms LeanCrypto.Proofs.MillerAlgebra.Cocycle.fourpoint
#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_add
#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_q_add
#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_zero
#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_nat_add

#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_three_coboundary
#print axioms LeanCrypto.Proofs.MillerAlgebra.miller_three_coboundary_q
