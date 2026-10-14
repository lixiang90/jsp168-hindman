import Hindman168.PredictionDualMomentDomination
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Weighted L1 transfer to centered tests

Original finite coefficients and the dominating density are retained.
Vanishing weighted L1 error transfers a centered expectation limit without
normalizing the weighted law or presuming a product bound.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem centered_mask_abs_le_one_add {ν : ℝ} (hν : 0 ≤ ν) : |ν - 1| ≤ 1 + ν := by
  apply abs_le.mpr
  constructor <;> linarith

theorem weighted_centered_difference_bound {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (c H f g : α → ℝ) (hc : ∀ x, |c x| ≤ H x) :
    |expectation μ (fun x => c x * f x) - expectation μ (fun x => c x * g x)| ≤
      expectation μ (fun x => H x * |f x - g x|) := by
  have he : expectation μ (fun x => c x * f x) - expectation μ (fun x => c x * g x) =
      expectation μ (fun x => c x * (f x - g x)) := by
    rw [← expectation_sub]
    apply congrArg (expectation μ)
    funext x
    ring
  rw [he]
  apply abs_expectation_le_majorant _ _ _ hμ
  intro x
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)

theorem weighted_centered_limit_transfer {α : Type*} (μ : ℕ → Mass α)
    (c H f g : ℕ → α → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hc : ∀ᶠ w in atTop, ∀ x, |c w x| ≤ H w x)
    (herr : Tendsto (fun w => expectation (μ w)
      (fun x => H w x * |f w x - g w x|)) atTop (𝓝 0))
    (hf : Tendsto (fun w => expectation (μ w) (fun x => c w x * f w x)) atTop (𝓝 0)) :
    Tendsto (fun w => expectation (μ w) (fun x => c w x * g w x)) atTop (𝓝 0) := by
  let a w := expectation (μ w) (fun x => c w x * f w x) -
    expectation (μ w) (fun x => c w x * g w x)
  have hb : ∀ᶠ w in atTop, |a w| ≤ expectation (μ w)
      (fun x => H w x * |f w x - g w x|) := by
    filter_upwards [hμ, hc] with w hw hcw
    exact weighted_centered_difference_bound (μ w) hw (c w) (H w) (f w) (g w) hcw
  have haAbs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb herr
  have ha : Tendsto a atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (by simpa only [Real.norm_eq_abs] using haAbs)
  have ht := hf.sub ha
  convert ht using 1 <;> simp [a]

end Hindman168
