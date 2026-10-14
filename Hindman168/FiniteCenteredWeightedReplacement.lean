import Hindman168.FiniteWeightedCauchySchwarz
import Mathlib.Analysis.Real.Sqrt

/-! Exact centered density expansion and weighted replacement. The
underlying finite mass may be unnormalized; positivity and domination
are needed only on its original support. -/

namespace Hindman168.FiniteMass

open Filter
open scoped BigOperators Topology Classical

theorem expectation_centered_weighted_square {α : Type*} (μ : Mass α)
    (B H : α → ℝ) (c : ℝ) :
    expectation μ (fun p => B p * (H p - c) ^ 2) =
      expectation μ (fun p => B p * H p ^ 2) -
        2 * c * expectation μ (fun p => B p * H p) + c ^ 2 * expectation μ B := by
  have he : (fun p => B p * (H p - c) ^ 2) =
      (fun p => (B p * H p ^ 2 - 2 * c * (B p * H p)) + c ^ 2 * B p) := by
    funext p
    ring
  rw [he, expectation_add, expectation_sub, expectation_const_mul, expectation_const_mul]

theorem weighted_centered_replacement_tendsto_zero {α : Type*}
    (μ : ℕ → Mass α) (G B H : ℕ → α → ℝ) (c L : ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ p, 0 ≤ μ w p)
    (hbound : ∀ᶠ w in atTop, ∀ p ∈ (μ w).support, |G w p| ≤ B w p)
    (hmean : Tendsto (fun w => expectation (μ w) (B w)) atTop (𝓝 L))
    (hvariance : Tendsto (fun w => expectation (μ w) (fun p => B w p * (H w p - c) ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun w => expectation (μ w) (fun p => G w p * (H w p - c))) atTop (𝓝 0) := by
  let e w := expectation (μ w) (fun p => G w p * (H w p - c))
  have hb : ∀ᶠ w in atTop, e w ^ 2 ≤ expectation (μ w) (B w) *
      expectation (μ w) (fun p => B w p * (H w p - c) ^ 2) := by
    filter_upwards [hμ, hbound] with w hw hbw
    simpa only [sq_abs] using
      finite_weighted_cauchy_schwarz (μ w) hw (G w) (B w) (fun p => H w p - c) hbw
  have hs : Tendsto (fun w => e w ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hb
      (by simpa only [mul_zero] using hmean.mul hvariance)
  have ha := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  change Tendsto (fun w => Real.sqrt (e w ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ha
  have hn : Tendsto (fun w => ‖e w‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ha
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem expectation_centered_product_eq {α : Type*} (μ : Mass α)
    (G H : α → ℝ) (c : ℝ) :
    expectation μ (fun p => G p * (H p - c)) =
      expectation μ (fun p => G p * H p) - c * expectation μ G := by
  have he : (fun p => G p * (H p - c)) = (fun p => G p * H p - c * G p) := by
    funext p
    ring
  rw [he, expectation_sub, expectation_const_mul]

end Hindman168.FiniteMass
