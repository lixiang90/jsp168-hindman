import Hindman168.NativePieceRecipes
import Hindman168.PieceNilLipschitzComposition

/-! The calibration cutoff used in the Prediction Principle. Its
composition uses the original quotient, orbit and metric. -/

namespace Hindman168
open NNReal
universe u

noncomputable def calibrationCutoff (τ x : ℝ) : ℝ := 1 - unitIntervalClip ((x - 2*τ) / τ)

theorem calibrationCutoff_bounds (τ x : ℝ) :
    0 ≤ calibrationCutoff τ x ∧ calibrationCutoff τ x ≤ 1 := by
  have h := unitIntervalClip_bounds ((x - 2*τ) / τ)
  unfold calibrationCutoff
  constructor <;> linarith

theorem calibrationCutoff_low (τ : ℝ) (hτ : 0 < τ) (x : ℝ) (hx : x ≤ 2*τ) :
    calibrationCutoff τ x = 1 := by
  have hd : (x - 2*τ) / τ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le
  simp only [calibrationCutoff, unitIntervalClip,
    min_eq_right (hd.trans zero_le_one), max_eq_left hd, sub_zero]

theorem calibrationCutoff_high (τ : ℝ) (hτ : 0 < τ) (x : ℝ) (hx : 3*τ ≤ x) :
    calibrationCutoff τ x = 0 := by
  have hd : 1 ≤ (x - 2*τ) / τ := (le_div_iff₀ hτ).mpr (by linarith)
  simp only [calibrationCutoff, unitIntervalClip, min_eq_left hd, max_eq_right zero_le_one, sub_self]

theorem calibrationCutoff_weight_bound (τ : ℝ) (hτ : 0 < τ) (x : ℝ) (hx : 0 ≤ x) :
    x * calibrationCutoff τ x ≤ 3*τ := by
  by_cases h : x ≤ 3*τ
  · exact (mul_le_mul_of_nonneg_left (calibrationCutoff_bounds τ x).2 hx).trans
      (by simpa only [mul_one] using h)
  · rw [calibrationCutoff_high τ hτ x (le_of_lt (lt_of_not_ge h)), mul_zero]
    positivity

theorem calibrationCutoff_lipschitz (τ : ℝ) (hτ : 0 < τ) :
    LipschitzWith ⟨τ⁻¹, inv_nonneg.mpr hτ.le⟩ (calibrationCutoff τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |calibrationCutoff τ x - calibrationCutoff τ y| ≤ τ⁻¹ * |x-y|
  have h := unitIntervalClip_lipschitz.dist_le_mul ((x - 2*τ) / τ) ((y - 2*τ) / τ)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  have he : (x - 2*τ) / τ - (y - 2*τ) / τ = (x-y) / τ := by ring
  rw [he, abs_div, abs_of_pos hτ] at h
  have hf : calibrationCutoff τ x - calibrationCutoff τ y =
    -(unitIntervalClip ((x - 2*τ) / τ) - unitIntervalClip ((y - 2*τ) / τ)) := by
    unfold calibrationCutoff
    ring
  simpa only [Real.dist_eq, hf, abs_neg, div_eq_mul_inv, mul_comm] using h

theorem nativePieceRepresented_calibrationCutoff {s N : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ)
    (hf : NativePieceRepresented.{u} s F gap f) (τ : ℝ) (hτ : 0 < τ) :
    NativePieceRepresented.{u} s F gap (fun w y => calibrationCutoff τ (f w y)) := by
  obtain ⟨D, hD⟩ := hf
  letI := D.metric
  exact ⟨D, boundedPieceNilsequence_lipschitz_comp D.Γ F gap f hD
    (calibrationCutoff τ) _ (calibrationCutoff_lipschitz τ hτ)⟩

end Hindman168
