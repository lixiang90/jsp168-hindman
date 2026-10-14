import Hindman168.NativeCalibrationCutoff
import Hindman168.FiniteWeightedErrors

namespace Hindman168
open FiniteMass
open scoped Classical

/-- A cutoff pairing controls the small-model color event without
normalizing its original weighted mass. -/
theorem finite_cutoff_calibration {α : Type*} (μ : Mass α)
    (hμ : ∀ y, 0 ≤ μ y) (hprob : total μ ≤ 1)
    (ρ model : α → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : ∀ y, 0 ≤ model y)
    (τ : ℝ) (hτ : 0 < τ) (ε : ℝ)
    (htest : |expectation μ (fun y => (ρ y - model y) * calibrationCutoff τ (model y))| < ε) :
    expectation μ (fun y => if model y ≤ 2*τ then ρ y else 0) < 3*τ + ε := by
  have hlow : expectation μ (fun y => if model y ≤ 2*τ then ρ y else 0) ≤
      expectation μ (fun y => ρ y * calibrationCutoff τ (model y)) := by
    apply expectation_mono _ _ _ hμ
    intro y
    split_ifs with h
    · rw [calibrationCutoff_low τ hτ _ h, mul_one]
    · exact mul_nonneg (hρ y) (calibrationCutoff_bounds τ _).1
  have hm' : expectation μ (fun y => model y * calibrationCutoff τ (model y)) ≤ 3*τ := by
    calc
      _ ≤ expectation μ (fun _ => 3*τ) := expectation_mono _ _ _ hμ
        (fun y => calibrationCutoff_weight_bound τ hτ _ (hm y))
      _ = total μ * (3*τ) := expectation_const _ _
      _ ≤ 3*τ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hprob (by positivity : 0 ≤ 3*τ)
  have he : expectation μ (fun y => ρ y * calibrationCutoff τ (model y)) =
      expectation μ (fun y => (ρ y - model y) * calibrationCutoff τ (model y)) +
      expectation μ (fun y => model y * calibrationCutoff τ (model y)) := by
    rw [← expectation_add]
    congr 1
    funext y
    ring
  have hh := le_abs_self (expectation μ
    (fun y => (ρ y - model y) * calibrationCutoff τ (model y)))
  rw [he] at hlow
  linarith

end Hindman168
