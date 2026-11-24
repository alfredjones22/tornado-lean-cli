import TornadoProofs.Witness.ReferenceControl
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace TornadoProofs.Witness.PedersenReference

theorem group_window_selection {G : Type} [AddCommGroup G] [Inhabited G]
    (bits : Nat → Nat) (offset : Nat) (base : G)
    (b0 : bits offset < 2) (b1 : bits (offset+1) < 2) (b2 : bits (offset+2) < 2) :
    windowWith (groupWindows bits) offset base =
      .ok (PedersenWindows.selectedWindow base (bits offset) (bits (offset+1)) (bits (offset+2)) (bits (offset+3)),
        (8 : Nat) • base) := by
  have bound : PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2)) < 8 := by
    unfold PedersenWindows.selectorIndex
    omega
  generalize indexEq : PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2)) = index at *
  interval_cases index
  all_goals by_cases signZero : bits (offset+3) = 0
  all_goals simp [windowWith, groupWindows, PedersenWindows.selectedWindow, indexEq, signZero,
    Std.Legacy.Range.forIn_eq_forIn_range', List.range', List.foldl]
  all_goals abel_nf
  all_goals rfl

theorem group_window_nativeNibble {G : Type} [AddCommGroup G] [Inhabited G]
    (bits : Nat → Nat) (offset : Nat) (base : G)
    (b0 : bits offset < 2) (b1 : bits (offset+1) < 2) (b2 : bits (offset+2) < 2) (b3 : bits (offset+3) < 2) :
    windowWith (groupWindows bits) offset base =
      .ok (LeanCrypto.Proofs.BabyJubjubWindows.nativeNibble
        (PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2)) + 8*bits (offset+3)) • base,
        (8 : Nat) • base) := by
  rw [group_window_selection bits offset base b0 b1 b2,
    PedersenWindows.selectedWindow_nativeNibble base _ _ _ _ b0 b1 b2 b3]

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.group_window_selection
#print axioms TornadoProofs.Witness.PedersenReference.group_window_nativeNibble
