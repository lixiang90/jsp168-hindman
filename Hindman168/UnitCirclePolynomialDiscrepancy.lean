import Hindman168.UnitCircleUniformFourierApproximation
import Hindman168.ScalarPolynomialPhaseLags

namespace Hindman168
open Polynomial MeasureTheory
open scoped BigOperators Classical Topology

noncomputable def unitCirclePolynomialDiscrepancy (p : ℝ[X]) (N : ℕ) : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := finiteComplexSetMean (Finset.range N) (fun n => F ((p.eval (n : ℝ) : ℝ) : UnitAddCircle)) -
    ∫ t, F t ∂AddCircle.haarAddCircle
  map_add' F G := by
    have hF := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
      (μ := AddCircle.haarAddCircle)
    have hG := G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
      (μ := AddCircle.haarAddCircle)
    simp only [ContinuousMap.add_apply, finiteComplexSetMean, Finset.sum_add_distrib,
      add_div, integral_add hF hG]
    ring
  map_smul' c F := by
    simp only [ContinuousMap.smul_apply, finiteComplexSetMean, ← Finset.smul_sum,
      smul_div_assoc, integral_smul, smul_sub, RingHom.id_apply]

theorem unit_circle_polynomial_discrepancy_apply (p : ℝ[X]) (N : ℕ) (F : C(UnitAddCircle, ℂ)) :
    unitCirclePolynomialDiscrepancy p N F =
      finiteComplexSetMean (Finset.range N) (fun n => F ((p.eval (n : ℝ) : ℝ) : UnitAddCircle)) -
        ∫ t, F t ∂AddCircle.haarAddCircle := rfl

theorem unit_circle_polynomial_discrepancy_norm_bound (p : ℝ[X]) (N : ℕ) (F : C(UnitAddCircle, ℂ)) :
    ‖unitCirclePolynomialDiscrepancy p N F‖ ≤ 2*‖F‖ := by
  have hm := finiteComplexSetMean_norm_bound (Finset.range N)
    (fun n => F ((p.eval (n : ℝ) : ℝ) : UnitAddCircle)) ‖F‖ (norm_nonneg F)
    (fun n _ => F.norm_coe_le_norm _)
  have hi : ‖∫ t, F t ∂AddCircle.haarAddCircle‖ ≤ ‖F‖ := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
        (Filter.Eventually.of_forall (fun t => F.norm_coe_le_norm t))
  exact (norm_sub_le _ _).trans (by linarith)

theorem unit_circle_polynomial_fourier_value (p : ℝ[X]) (n : ℕ) (k : ℤ) :
    fourier k ((p.eval (n : ℝ) : ℝ) : UnitAddCircle) = scalarPolynomialPhase (C (k : ℝ)*p) n := by
  rw [fourier_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  simp only [scalarPolynomialPhase, eval_mul, eval_C]

theorem unit_circle_polynomial_nonzero_fourier_discrepancy (p : ℝ[X]) (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    unitCirclePolynomialDiscrepancy p N (fourier k) =
      finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase (C (k : ℝ)*p)) := by
  rw [unit_circle_polynomial_discrepancy_apply, unit_circle_fourier_haar_integral, if_neg hk, sub_zero]
  have he : (fun n : ℕ => fourier k ((p.eval (n : ℝ) : ℝ) : UnitAddCircle)) =
      scalarPolynomialPhase (C (k : ℝ)*p) := funext (fun n => unit_circle_polynomial_fourier_value p n k)
  rw [he]

theorem unit_circle_polynomial_zero_fourier_discrepancy (p : ℝ[X]) (N : ℕ) (hN : 0 < N) :
    unitCirclePolynomialDiscrepancy p N (fourier 0) = 0 := by
  rw [unit_circle_polynomial_discrepancy_apply, unit_circle_fourier_haar_integral, if_pos rfl]
  simp only [fourier_zero, finiteComplexSetMean, Finset.sum_const, nsmul_eq_mul,
    Finset.card_range, mul_one]
  rw [div_self (by exact_mod_cast hN.ne'), sub_self]

end Hindman168
