import Hindman168.FiniteComplexSetMean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Exact scaling of a finite mean minus a genuine measure integral. -/
namespace Hindman168
open MeasureTheory

theorem complex_mean_integral_scale {α X : Type*} [MeasurableSpace X]
    (S : Finset α) (x : α → X) (μ : Measure X) (f : X → ℂ) (c : ℂ) :
    finiteComplexSetMean S (fun a => c • f (x a)) - ∫ y, c • f y ∂μ =
      c • (finiteComplexSetMean S (fun a => f (x a)) - ∫ y, f y ∂μ) := by
  simp only [finiteComplexSetMean,← Finset.smul_sum,smul_div_assoc,integral_smul,smul_sub]

theorem complex_mean_integral_normalization_norm {α X : Type*} [MeasurableSpace X]
    (S : Finset α) (x : α → X) (μ : Measure X) (f : X → ℂ) (R : ℝ) (hR : 0 < R) :
    ‖finiteComplexSetMean S (fun a => (R : ℂ)⁻¹ • f (x a)) - ∫ y, (R : ℂ)⁻¹ • f y ∂μ‖ =
      R⁻¹ * ‖finiteComplexSetMean S (fun a => f (x a)) - ∫ y, f y ∂μ‖ := by
  rw [complex_mean_integral_scale,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]

end Hindman168
