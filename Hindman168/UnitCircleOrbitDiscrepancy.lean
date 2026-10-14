import Hindman168.UnitCircleUniformFourierApproximation
import Hindman168.UnitCircleGeometricMean

namespace Hindman168
open scoped BigOperators Classical Topology
open MeasureTheory

noncomputable def unitCircleOrbitDiscrepancy (x : ℝ) (N : ℕ) : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := finiteComplexSetMean (Finset.range N) (fun n => F (((n : ℝ)*x : ℝ) : UnitAddCircle)) -
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

theorem unit_circle_orbit_discrepancy_apply (x : ℝ) (N : ℕ) (F : C(UnitAddCircle, ℂ)) :
    unitCircleOrbitDiscrepancy x N F = finiteComplexSetMean (Finset.range N)
      (fun n => F (((n : ℝ)*x : ℝ) : UnitAddCircle)) - ∫ t, F t ∂AddCircle.haarAddCircle := rfl

theorem unit_circle_orbit_discrepancy_norm_bound (x : ℝ) (N : ℕ) (F : C(UnitAddCircle, ℂ)) :
    ‖unitCircleOrbitDiscrepancy x N F‖ ≤ 2*‖F‖ := by
  have hm := finiteComplexSetMean_norm_bound (Finset.range N)
    (fun n => F (((n : ℝ)*x : ℝ) : UnitAddCircle)) ‖F‖ (norm_nonneg F)
    (fun n _ => F.norm_coe_le_norm _)
  have hi : ‖∫ t, F t ∂AddCircle.haarAddCircle‖ ≤ ‖F‖ := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
        (Filter.Eventually.of_forall (fun t => F.norm_coe_le_norm t))
  exact (norm_sub_le _ _).trans (by linarith)

theorem unit_circle_fourier_orbit_value (x : ℝ) (n : ℕ) (k : ℤ) :
    fourier k (((n : ℝ)*x : ℝ) : UnitAddCircle) =
      (AddCircle.toCircle (((n : ℝ)*((k : ℝ)*x) : ℝ) : UnitAddCircle) : ℂ) := by
  rw [fourier_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [show (k : ℝ)*((n : ℝ)*x) = (n : ℝ)*((k : ℝ)*x) by ring]

theorem unit_circle_nonzero_fourier_discrepancy (x : ℝ) (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    unitCircleOrbitDiscrepancy x N (fourier k) = finiteComplexSetMean (Finset.range N)
      (fun n => (AddCircle.toCircle (((n : ℝ)*((k : ℝ)*x) : ℝ) : UnitAddCircle) : ℂ)) := by
  rw [unit_circle_orbit_discrepancy_apply]
  rw [unit_circle_fourier_haar_integral, if_neg hk, sub_zero]
  congr 1
  funext n
  exact unit_circle_fourier_orbit_value x n k

theorem unit_circle_zero_fourier_discrepancy (x : ℝ) (N : ℕ) (hN : 0 < N) :
    unitCircleOrbitDiscrepancy x N (fourier 0) = 0 := by
  rw [unit_circle_orbit_discrepancy_apply, unit_circle_fourier_haar_integral, if_pos rfl]
  simp only [fourier_zero,
    finiteComplexSetMean, Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_one]
  rw [div_self (by exact_mod_cast hN.ne'), sub_self]

end Hindman168
