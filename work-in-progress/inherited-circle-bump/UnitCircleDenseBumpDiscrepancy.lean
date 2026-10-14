import Hindman168.UnitCircleNormBump

namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical

theorem unit_circle_dense_norm_bump_discrepancy (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x b : ℝ) (N : ℕ) (hN : 0 < N) (eps : ℝ) (heps : eps ≤ δ/10)
    (hdense : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n =>
      ‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖ ≤ eps)).card) :
    δ^2/64 ≤ ‖finiteComplexSetMean (Finset.range N)
      (fun n => unitCircleComplexNormBump (δ/4) (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) -
        ∫ t, unitCircleComplexNormBump (δ/4) t ∂AddCircle.haarAddCircle‖ := by
  let c := δ/4
  let v : ℕ → ℝ := fun n => unitCircleNormBump c (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))
  let S := (Finset.range N).filter (fun n => ‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖ ≤ eps)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have ha : 0 ≤ c-eps := by dsimp only [c]; linarith
  have hsum : (S.card : ℝ)*(c-eps) ≤ ∑ n ∈ Finset.range N, v n := by
    calc
      _ = ∑ n ∈ Finset.range N,
          (if ‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖ ≤ eps then c-eps else 0) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, S]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : ‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖ ≤ eps
        · rw [if_pos hn]
          exact (by linarith : c-eps ≤ c-‖(((b+(n : ℝ)*x : ℝ) : UnitAddCircle))‖).trans
            (le_max_right _ _)
        · rw [if_neg hn]
          exact (unit_circle_norm_bump_bounds c hc _).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : δ*(c-eps) ≤ (∑ n ∈ Finset.range N, v n)/(N : ℝ) := by
    apply (le_div_iff₀ hNr).mpr
    have h := mul_le_mul_of_nonneg_right hdense ha
    change δ*(N : ℝ)*(c-eps) ≤ (S.card : ℝ)*(c-eps) at h
    nlinarith
  have hI : (∫ t, unitCircleNormBump c t ∂AddCircle.haarAddCircle) ≤ 2*c^2 :=
    unit_circle_norm_bump_integral_bound c hc (by dsimp only [c]; linarith)
  have hgap : δ^2/64 ≤ (∑ n ∈ Finset.range N, v n)/(N : ℝ) -
      ∫ t, unitCircleNormBump c t ∂AddCircle.haarAddCircle := by
    dsimp only [c] at hm hI
    nlinarith [mul_le_mul_of_nonneg_left heps hδ.le]
  have hmean : finiteComplexSetMean (Finset.range N)
      (fun n => unitCircleComplexNormBump c (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) =
      (((∑ n ∈ Finset.range N, v n)/(N : ℝ) : ℝ) : ℂ) := by
    change (∑ n ∈ Finset.range N, (v n : ℂ))/(N : ℂ) = _
    push_cast
    rfl
  have hInt : (∫ t, unitCircleComplexNormBump c t ∂AddCircle.haarAddCircle) =
      ((∫ t, unitCircleNormBump c t ∂AddCircle.haarAddCircle : ℝ) : ℂ) :=
    integral_complex_ofReal
  change δ^2/64 ≤ ‖finiteComplexSetMean (Finset.range N)
    (fun n => unitCircleComplexNormBump c (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) - _‖
  rw [hmean, hInt, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hgap.trans (le_abs_self _)

end Hindman168
