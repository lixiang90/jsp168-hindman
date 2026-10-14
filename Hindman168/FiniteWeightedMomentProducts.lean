import Hindman168.FiniteWeightedCauchySchwarz
import Hindman168.PredictionClippingMoments
import Mathlib.Analysis.Real.Sqrt

/-!
# Bounded fixed moments of products under an unnormalized weighted law

The density is kept in every finite coefficient. Repeated weighted
Cauchy--Schwarz derives product moments from single-factor moments.
No probability normalization or independence is assumed.
-/

namespace Hindman168.FiniteMass

open Filter
open scoped BigOperators Topology Classical

noncomputable def WeightedMomentBounded {α : Type*} (μ : ℕ → Mass α)
    (H f : ℕ → α → ℝ) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in atTop,
    expectation (μ w) (fun x => H w x * |f w x| ^ p) ≤ C

theorem weighted_product_cauchy_schwarz {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (H f g : α → ℝ) (hH : ∀ x, 0 ≤ H x) :
    (expectation μ (fun x => H x * (f x * g x))) ^ 2 ≤
      expectation μ (fun x => H x * f x ^ 2) *
        expectation μ (fun x => H x * g x ^ 2) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul μ.support
    (r := fun x => μ x * (H x * (f x * g x)))
    (f := fun x => μ x * (H x * f x ^ 2))
    (g := fun x => μ x * (H x * g x ^ 2))
    (fun x _ => mul_nonneg (hμ x) (mul_nonneg (hH x) (sq_nonneg _)))
    (fun x _ => mul_nonneg (hμ x) (mul_nonneg (hH x) (sq_nonneg _)))
    (fun _ _ => by ring_nf; exact le_rfl)
  exact hc

theorem weighted_moment_one {α : Type*} (μ : ℕ → Mass α) (H : ℕ → α → ℝ)
    (hbase : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in atTop, expectation (μ w) (H w) ≤ C) :
    WeightedMomentBounded μ H (fun _ _ => 1) := by
  intro p
  obtain ⟨C, hC, hb⟩ := hbase
  refine ⟨C, hC, ?_⟩
  simpa only [abs_one, one_pow, mul_one] using hb

theorem weighted_moment_mul {α : Type*} (μ : ℕ → Mass α) (H f g : ℕ → α → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hH : ∀ᶠ w in atTop, ∀ x, 0 ≤ H w x)
    (hf : WeightedMomentBounded μ H f) (hg : WeightedMomentBounded μ H g) :
    WeightedMomentBounded μ H (fun w x => f w x * g w x) := by
  intro p
  obtain ⟨Cf, hCf, hfb⟩ := hf (2 * p)
  obtain ⟨Cg, hCg, hgb⟩ := hg (2 * p)
  refine ⟨1 + Cf * Cg, by positivity, ?_⟩
  filter_upwards [hμ, hH, hfb, hgb] with w hw hHw hfw hgw
  let e := expectation (μ w) (fun x => H w x * |f w x * g w x| ^ p)
  have hc := weighted_product_cauchy_schwarz (μ w) hw (H w)
    (fun x => |f w x| ^ p) (fun x => |g w x| ^ p) hHw
  have hg0 : 0 ≤ expectation (μ w) (fun x => H w x * |g w x| ^ (2 * p)) :=
    expectation_nonneg _ _ hw (fun x => mul_nonneg (hHw x) (pow_nonneg (abs_nonneg _) _))
  have hc' : e ^ 2 ≤ Cf * Cg := by
    have heq : (fun x => H w x * (|f w x| ^ p * |g w x| ^ p)) =
        (fun x => H w x * |f w x * g w x| ^ p) := by
      funext x
      rw [abs_mul, mul_pow]
    rw [heq] at hc
    simp only [← pow_mul, Nat.mul_comm p 2] at hc
    exact hc.trans (mul_le_mul hfw hgw hg0 hCf)
  change e ≤ _
  nlinarith [mul_nonneg hCf hCg, sq_nonneg (Cf * Cg)]

theorem weighted_moment_finset_prod {α ι : Type*} (μ : ℕ → Mass α)
    (H : ℕ → α → ℝ) (f : ι → ℕ → α → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hH : ∀ᶠ w in atTop, ∀ x, 0 ≤ H w x)
    (hbase : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in atTop, expectation (μ w) (H w) ≤ C)
    (hf : ∀ q, WeightedMomentBounded μ H (f q)) (U : Finset ι) :
    WeightedMomentBounded μ H (fun w x => ∏ q ∈ U, f q w x) := by
  induction U using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weighted_moment_one μ H hbase
  | @insert q U hq ih =>
    simpa only [Finset.prod_insert hq] using weighted_moment_mul μ H (f q)
      (fun w x => ∏ r ∈ U, f r w x) hμ hH (hf q) ih

theorem weighted_l2_product_tendsto {α : Type*} (μ : ℕ → Mass α)
    (H f g : ℕ → α → ℝ)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (hH : ∀ᶠ w in atTop, ∀ x, 0 ≤ H w x)
    (hf : Tendsto (fun w => expectation (μ w) (fun x => H w x * |f w x| ^ 2)) atTop (𝓝 0))
    (Cg : ℝ) (_hCg : 0 ≤ Cg)
    (hg : ∀ᶠ w in atTop, expectation (μ w) (fun x => H w x * |g w x| ^ 2) ≤ Cg) :
    Tendsto (fun w => expectation (μ w) (fun x => H w x * |f w x * g w x|)) atTop (𝓝 0) := by
  let e w := expectation (μ w) (fun x => H w x * |f w x * g w x|)
  have hb : ∀ᶠ w in atTop, e w ^ 2 ≤
      expectation (μ w) (fun x => H w x * |f w x| ^ 2) * Cg := by
    filter_upwards [hμ, hH, hg] with w hw hHw hgw
    have hc := weighted_product_cauchy_schwarz (μ w) hw (H w)
      (fun x => |f w x|) (fun x => |g w x|) hHw
    simp only [← abs_mul] at hc
    have h0 : 0 ≤ expectation (μ w) (fun x => H w x * |f w x| ^ 2) :=
      expectation_nonneg _ _ hw (fun x => mul_nonneg (hHw x) (pow_nonneg (abs_nonneg _) _))
    exact hc.trans (mul_le_mul_of_nonneg_left hgw h0)
  have hs : Tendsto (fun w => e w ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hb
      (by simpa only [zero_mul] using hf.mul_const Cg)
  have ha := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  change Tendsto (fun w => Real.sqrt (e w ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ha
  have hnorm : Tendsto (fun w => ‖e w‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ha
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end Hindman168.FiniteMass
