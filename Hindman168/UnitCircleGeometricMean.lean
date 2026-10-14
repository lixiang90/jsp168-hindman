import Hindman168.UnitCirclePhaseDistance
import Hindman168.FiniteComplexSetMean
import Mathlib.Algebra.Ring.GeomSum

namespace Hindman168
open scoped BigOperators Classical

theorem unit_circle_geometric_sum_bound (z : Circle) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (z : ℂ)^n‖*‖(z : ℂ)-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  have h := norm_sub_le ((z : ℂ)^N) 1
  simpa only [norm_pow, Circle.norm_coe, one_pow, norm_one, one_add_one_eq_two] using h

/-- A genuine finite phase average estimate, including resonant phases. -/
theorem unit_circle_linear_mean_mod_one_bound (x : ℝ) (N : ℕ) :
    (N : ℝ)*‖finiteComplexSetMean (Finset.range N)
      (fun n => (AddCircle.toCircle (((n : ℝ)*x : ℝ) : UnitAddCircle) : ℂ))‖*
        ‖(x : UnitAddCircle)‖ ≤ (1 : ℝ)/2 := by
  let z := AddCircle.toCircle (x : UnitAddCircle)
  have hsum : 4*(‖∑ n ∈ Finset.range N, (z : ℂ)^n‖*‖(x : UnitAddCircle)‖) ≤ 2 := by
    have hd := mul_le_mul_of_nonneg_left (unit_circle_phase_distance_lower x)
      (norm_nonneg (∑ n ∈ Finset.range N, (z : ℂ)^n))
    have hg := unit_circle_geometric_sum_bound z N
    nlinarith
  by_cases hN : N = 0
  · simp only [hN, Nat.cast_zero, zero_mul]
    norm_num
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmean : ‖finiteComplexSetMean (Finset.range N)
      (fun n => (AddCircle.toCircle (((n : ℝ)*x : ℝ) : UnitAddCircle) : ℂ))‖ =
      ‖∑ n ∈ Finset.range N, (z : ℂ)^n‖/(N : ℝ) := by
    simp only [finiteComplexSetMean, unit_circle_phase_natural_mul, Finset.card_range,
      norm_div, Complex.norm_natCast, z]
  rw [hmean]
  have heq : (N : ℝ)*(‖∑ n ∈ Finset.range N, (z : ℂ)^n‖/(N : ℝ))*
      ‖(x : UnitAddCircle)‖ = ‖∑ n ∈ Finset.range N, (z : ℂ)^n‖*‖(x : UnitAddCircle)‖ := by
    field_simp
  rw [heq]
  linarith

theorem unit_circle_large_linear_mean_inverse (x : ℝ) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ)
    (hlarge : δ ≤ ‖finiteComplexSetMean (Finset.range N)
      (fun n => (AddCircle.toCircle (((n : ℝ)*x : ℝ) : UnitAddCircle) : ℂ))‖) :
    ‖(x : UnitAddCircle)‖ ≤ 1/(2*δ*(N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := unit_circle_linear_mean_mod_one_bound x N
  have hm := mul_le_mul_of_nonneg_left hlarge hNr.le
  have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (x : UnitAddCircle))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*δ*(N : ℝ))).mpr
  nlinarith

end Hindman168
