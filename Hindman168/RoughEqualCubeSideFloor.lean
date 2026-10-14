import Hindman168.RoughEqualCubeHaarSelection

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_cube_side_floor (lam Z : ℝ) (hlam : 0 < lam) (hZ : 0 < Z)
    (hlarge : 2 ≤ lam*Z) :
    0 < ⌊lam*Z⌋₊ ∧ lam*Z/2 ≤ (⌊lam*Z⌋₊ : ℝ) ∧ (⌊lam*Z⌋₊ : ℝ) ≤ lam*Z := by
  have hlo := Nat.lt_floor_add_one (lam*Z)
  have hhi := Nat.floor_le (le_of_lt (mul_pos hlam hZ))
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, hhi⟩
  linarith

theorem rough_equal_cube_side_floor_fits {κ : Type*}
    (width : κ → ℕ) (c lam Z : ℝ) (hlam : 0 < lam) (hZ : 0 < Z)
    (hlamc : lam ≤ c) (hwidth : ∀ j, c*Z ≤ (width j : ℝ)) :
    ∀ j, ⌊lam*Z⌋₊ ≤ width j := by
  intro j
  have hN := Nat.floor_le (le_of_lt (mul_pos hlam hZ))
  have hj := hwidth j
  have hh : (⌊lam*Z⌋₊ : ℝ) ≤ width j :=
    hN.trans ((mul_le_mul_of_nonneg_right hlamc hZ.le).trans hj)
  exact_mod_cast hh

end Hindman168
