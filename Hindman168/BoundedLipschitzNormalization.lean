import Hindman168.CompactUnitLipschitzObservables
import Hindman168.LinearDiscrepancyStability

/-! Genuine common scaling into unit observables, with exact linear discrepancy. -/

namespace Hindman168

theorem bounded_lipschitz_normalization (X : Type*) [MetricSpace X]
    (F : C(X, ℂ)) (B L R : ℝ) (hR : 0 < R) (hBR : B ≤ R) (hLR : L ≤ R)
    (hNorm : ∀ x, ‖F x‖ ≤ B) (hLip : LipschitzWith (Real.toNNReal L) F) :
    ((R : ℂ)⁻¹ • F) ∈ unitLipschitzObservables X := by
  have hc : ‖(R : ℂ)⁻¹‖ = R⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  constructor
  · apply LipschitzWith.mk_one
    intro x y
    have hLR' : (Real.toNNReal L : ℝ) ≤ R := by
      by_cases hL : 0 ≤ L
      · rw [Real.coe_toNNReal L hL]
        exact hLR
      · rw [Real.toNNReal_of_nonpos (le_of_not_ge hL)]
        exact hR.le
    have hf := hLip.dist_le_mul x y
    change dist ((R : ℂ)⁻¹ • F x) ((R : ℂ)⁻¹ • F y) ≤ dist x y
    rw [dist_eq_norm, ← smul_sub, norm_smul, hc]
    rw [dist_eq_norm] at hf
    have hd := dist_nonneg (x := x) (y := y)
    apply (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hR.le)).trans
    calc
      R⁻¹ * ((Real.toNNReal L : ℝ) * dist x y) ≤ R⁻¹ * (R * dist x y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLR' hd) (inv_nonneg.mpr hR.le)
      _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  · intro x
    change ‖(R : ℂ)⁻¹ • F x‖ ≤ 1
    rw [norm_smul, hc]
    calc
      R⁻¹ * ‖F x‖ ≤ R⁻¹ * R :=
        mul_le_mul_of_nonneg_left ((hNorm x).trans hBR) (inv_nonneg.mpr hR.le)
      _ = 1 := inv_mul_cancel₀ hR.ne'

theorem linear_discrepancy_normalization_norm (X : Type*) [MetricSpace X]
    (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (F : C(X, ℂ)) (R : ℝ) (hR : 0 < R) :
    ‖Λ ((R : ℂ)⁻¹ • F)‖ = R⁻¹ * ‖Λ F‖ := by
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]

end Hindman168
