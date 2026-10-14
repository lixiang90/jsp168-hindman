import Hindman168.CompactUnitLipschitzObservables
import Hindman168.FiniteComplexSetMean
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Hindman168
open MeasureTheory
open scoped Topology

theorem bounded_complex_observable_normalization {X : Type*} [PseudoMetricSpace X]
    (F : C(X, ℂ)) (B R : ℝ) (L : NNReal) (hR : 0 < R) (hBR : B ≤ R) (hLR : (L : ℝ) ≤ R)
    (hF : LipschitzWith L F) (hB : ∀ x, ‖F x‖ ≤ B) :
    (R⁻¹ • F) ∈ unitLipschitzObservables X := by
  have hc : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hcL : R⁻¹*(L : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hR).mpr hLR
  have hcB : R⁻¹*B ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hR).mpr hBR
  refine ⟨LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    change dist (R⁻¹ • F x) (R⁻¹ • F y) ≤ (1 : NNReal)*dist x y
    calc
      _ = R⁻¹*dist (F x) (F y) := by
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, dist_eq_norm]
      _ ≤ R⁻¹*((L : ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hF.dist_le_mul x y) hc
      _ ≤ dist x y := by
        rw [← mul_assoc]
        exact (mul_le_mul_of_nonneg_right hcL (dist_nonneg : 0 ≤ dist x y)).trans_eq (one_mul _)
      _ = _ := by simp only [NNReal.coe_one, one_mul]
  · intro x
    change ‖R⁻¹ • F x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left (hB x) hc).trans hcB

theorem finite_complex_set_mean_real_smul {α : Type*} (s : Finset α) (f : α → ℂ) (c : ℝ) :
    finiteComplexSetMean s (fun x => c • f x) = c • finiteComplexSetMean s f := by
  simp only [finiteComplexSetMean, ← Finset.smul_sum, smul_div_assoc]

theorem finite_haar_discrepancy_real_smul {α X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset α) (f : α → X) (F : X → ℂ) (c : ℝ) :
    finiteComplexSetMean s (fun x => c • F (f x)) - (∫ q, c • F q ∂μ) =
      c • (finiteComplexSetMean s (fun x => F (f x)) - ∫ q, F q ∂μ) := by
  rw [finite_complex_set_mean_real_smul, integral_smul, smul_sub]

end Hindman168
