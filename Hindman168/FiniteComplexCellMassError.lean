import Hindman168.FiniteComplexSetMean
import Mathlib.Algebra.BigOperators.Field

/-! Actual cell means with proved mass discrepancies control the original
sum divided by its real scale. No exact equidistribution of cell sizes is
assumed; both the local mean and the cardinality error are retained. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_cell_mass_error {I Z : Type*} [Fintype I]
    (S : I → Finset Z) (a : Z → ℂ) (g : I → ℂ)
    (L w ε η : ℝ) (hL : 0 < L) (hε : 0 ≤ ε)
    (hmean : ∀ i, ‖finiteComplexSetMean (S i) a-g i‖ ≤ ε)
    (hmass : ∀ i, |((S i).card : ℝ)/L-w| ≤ η)
    (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(∑ i, ∑ z ∈ S i, a z)/(L : ℂ) - ∑ i, (w : ℂ)*g i‖ ≤
      (Fintype.card I : ℝ)*((w+η)*ε+η) := by
  have hcell (i : I) : ‖(∑ z ∈ S i, a z)/(L : ℂ)-(w : ℂ)*g i‖ ≤ (w+η)*ε+η := by
    have hnon : 0 ≤ ((S i).card : ℝ)/L := div_nonneg (Nat.cast_nonneg _) hL.le
    have hupper : ((S i).card : ℝ)/L ≤ w+η := by linarith [(abs_le.mp (hmass i)).2]
    have he : (∑ z ∈ S i, a z)/(L : ℂ)-(w : ℂ)*g i =
        (((S i).card : ℝ)/L : ℂ)*(finiteComplexSetMean (S i) a-g i) +
          ((((S i).card : ℝ)/L-w : ℝ) : ℂ)*g i := by
      rw [← finiteComplexSetMean_mul_card (S i) a]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ ‖(((S i).card : ℝ)/L : ℂ)*(finiteComplexSetMean (S i) a-g i)‖ +
          ‖((((S i).card : ℝ)/L-w : ℝ) : ℂ)*g i‖ := norm_add_le _ _
      _ = (((S i).card : ℝ)/L)*‖finiteComplexSetMean (S i) a-g i‖ +
          |((S i).card : ℝ)/L-w| * ‖g i‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (S i).card), abs_of_pos hL]
      _ ≤ (w+η)*ε+η*1 := add_le_add
        ((mul_le_mul_of_nonneg_left (hmean i) hnon).trans (mul_le_mul_of_nonneg_right hupper hε))
        (mul_le_mul (hmass i) (hg i) (norm_nonneg _) ((abs_nonneg _).trans (hmass i)))
      _ = _ := by ring
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(∑ z ∈ S i, a z)/(L : ℂ)-(w : ℂ)*g i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ((w+η)*ε+η) := Finset.sum_le_sum (fun i _ => hcell i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Hindman168
