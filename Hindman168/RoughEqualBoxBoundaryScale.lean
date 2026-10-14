import Hindman168.RoughEqualBoxBoundaryFraction

namespace Hindman168
open scoped BigOperators Classical

theorem rough_equal_box_boundary_fraction_scaled {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (width : κ → ℕ) (N : ℕ) (hN : 0 < N)
    (c Z lam : ℝ) (hc : 0 < c) (hZ : 0 < Z)
    (hwidth : ∀ j, c*Z ≤ (width j : ℝ)) (hside : (N : ℝ) ≤ lam*Z) :
    (((roughIntegerWidthBox a width \ roughEqualTiledBox a width N).card : ℝ)/
      (roughIntegerWidthBox a width).card) ≤ (Fintype.card κ : ℝ)*lam/c := by
  have hwpos : ∀ j, 0 < width j := fun j => by
    have hj : (0 : ℝ) < width j := (mul_pos hc hZ).trans_le (hwidth j)
    exact_mod_cast hj
  apply (rough_equal_box_boundary_fraction_side a width N hN hwpos).trans
  calc
    _ ≤ ∑ _j : κ, lam/c := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ (N : ℝ)/(c*Z) := div_le_div_of_nonneg_left (by positivity) (mul_pos hc hZ) (hwidth j)
        _ ≤ (lam*Z)/(c*Z) := div_le_div_of_nonneg_right hside (le_of_lt (mul_pos hc hZ))
        _ = _ := by field_simp [hc.ne', hZ.ne']
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Hindman168
