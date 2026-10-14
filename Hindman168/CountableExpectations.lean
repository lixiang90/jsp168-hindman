import Hindman168.CountableProductPMF
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Genuine countable nonnegative expectations and product factorization

The original PMF coefficients are retained in every sum. Nonnegative
extended expectations give pushforward invariance and independent-product
factorization; finiteness of the original local moments then proves real
summability of the corresponding joint expectations.
-/

namespace Hindman168.DiscreteProduct

open scoped BigOperators Classical ENNReal

noncomputable def expectation {α : Type*} (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, (μ a).toReal * f a

noncomputable def ennExpectation {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, μ a * f a

theorem weighted_ofReal {α : Type*} (μ : PMF α) (f : α → ℝ)
    (a : α) :
    μ a * ENNReal.ofReal (f a) = ENNReal.ofReal ((μ a).toReal * f a) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (μ.apply_ne_top a)]

theorem expectation_eq_toReal {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    expectation μ f = (ennExpectation μ (fun a => ENNReal.ofReal (f a))).toReal := by
  unfold expectation ennExpectation
  rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (μ.apply_ne_top a) ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]

theorem ennExpectation_ne_top {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hs : Summable (fun a => (μ a).toReal * f a)) :
    ennExpectation μ (fun a => ENNReal.ofReal (f a)) ≠ ∞ := by
  unfold ennExpectation
  simp_rw [weighted_ofReal μ f]
  exact hs.tsum_ofReal_ne_top

theorem weighted_summable_of_ennExpectation_ne_top {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a)
    (hs : ennExpectation μ (fun a => ENNReal.ofReal (f a)) ≠ ∞) :
    Summable (fun a => (μ a).toReal * f a) := by
  have h := ENNReal.summable_toReal hs
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)] using h

theorem ennExpectation_map {α β : Type*} (μ : PMF α) (stat : α → β) (f : β → ℝ≥0∞) :
    ennExpectation (μ.map stat) f = ennExpectation μ (fun a => f (stat a)) := by
  classical
  unfold ennExpectation
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (stat a)]
  · simp
  · intro b hb
    simp only [if_neg hb, zero_mul]

theorem expectation_map {α β : Type*} (μ : PMF α) (stat : α → β) (f : β → ℝ)
    (hf : ∀ b, 0 ≤ f b) :
    expectation (μ.map stat) f = expectation μ (fun a => f (stat a)) := by
  rw [expectation_eq_toReal _ _ hf, ennExpectation_map,
    expectation_eq_toReal _ _ (fun a => hf (stat a))]

theorem weighted_summable_map_pullback {α β : Type*} (μ : PMF α) (stat : α → β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b)
    (hs : Summable (fun b => ((μ.map stat) b).toReal * f b)) :
    Summable (fun a => (μ a).toReal * f (stat a)) := by
  apply weighted_summable_of_ennExpectation_ne_top _ _ (fun a => hf (stat a))
  rw [← ennExpectation_map μ stat (fun b => ENNReal.ofReal (f b))]
  exact ennExpectation_ne_top (μ.map stat) f hs

theorem weighted_mass_summable {α : Type*} (μ : PMF α) : Summable (fun a => (μ a).toReal) :=
  ENNReal.summable_toReal μ.tsum_coe_ne_top

theorem expectation_one {α : Type*} (μ : PMF α) : expectation μ (fun _ => 1) = 1 := by
  unfold expectation
  simp only [mul_one, ← ENNReal.tsum_toReal_eq μ.apply_ne_top, PMF.tsum_coe, ENNReal.toReal_one]

theorem weighted_one_add_summable {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hs : Summable (fun a => (μ a).toReal * f a)) :
    Summable (fun a => (μ a).toReal * (1 + f a)) := by
  simpa only [mul_add, mul_one] using (weighted_mass_summable μ).add hs

theorem expectation_one_add {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hs : Summable (fun a => (μ a).toReal * f a)) :
    expectation μ (fun a => 1 + f a) = 1 + expectation μ f := by
  unfold expectation
  simp only [mul_add, mul_one]
  rw [Summable.tsum_add (weighted_mass_summable μ) hs]
  simpa only [expectation, mul_one] using congrArg (fun x => x + ∑' a, (μ a).toReal * f a)
    (expectation_one μ)

theorem piPMF_ennExpectation_product {ι α : Type*} [Fintype ι]
    (μ : ι → PMF α) (f : ι → α → ℝ≥0∞) :
    ennExpectation (piPMF μ) (fun x => ∏ i, f i (x i)) =
      ∏ i, ennExpectation (μ i) (f i) := by
  unfold ennExpectation
  simp only [piPMF_apply, ← Finset.prod_mul_distrib]
  exact ennreal_product_tsum (fun i a => μ i a * f i a)

theorem piPMF_product_summable {ι α : Type*} [Fintype ι]
    (μ : ι → PMF α) (f : ι → α → ℝ) (hf : ∀ i a, 0 ≤ f i a)
    (hs : ∀ i, Summable (fun a => (μ i a).toReal * f i a)) :
    Summable (fun x => (piPMF μ x).toReal * ∏ i, f i (x i)) := by
  apply weighted_summable_of_ennExpectation_ne_top _ _
    (fun x => Finset.prod_nonneg (fun i _ => hf i (x i)))
  have he : (fun x : ι → α => ENNReal.ofReal (∏ i, f i (x i))) =
      (fun x => ∏ i, ENNReal.ofReal (f i (x i))) := by
    funext x
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hf i (x i))
  rw [he, piPMF_ennExpectation_product μ (fun i a => ENNReal.ofReal (f i a))]
  exact ENNReal.prod_ne_top (fun i _ => ennExpectation_ne_top (μ i) (f i) (hs i))

theorem piPMF_expectation_product {ι α : Type*} [Fintype ι]
    (μ : ι → PMF α) (f : ι → α → ℝ) (hf : ∀ i a, 0 ≤ f i a) :
    expectation (piPMF μ) (fun x => ∏ i, f i (x i)) =
      ∏ i, expectation (μ i) (f i) := by
  rw [expectation_eq_toReal _ _ (fun x => Finset.prod_nonneg (fun i _ => hf i (x i)))]
  have he : (fun x : ι → α => ENNReal.ofReal (∏ i, f i (x i))) =
      (fun x => ∏ i, ENNReal.ofReal (f i (x i))) := by
    funext x
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hf i (x i))
  rw [he, piPMF_ennExpectation_product μ (fun i a => ENNReal.ofReal (f i a)), ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => (expectation_eq_toReal (μ i) (f i) (hf i)).symm)

theorem expectation_sub_one {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hs : Summable (fun a => (μ a).toReal * f a)) :
    expectation μ (fun a => f a - 1) = expectation μ f - 1 := by
  unfold expectation
  simp only [mul_sub, mul_one]
  rw [Summable.tsum_sub hs (weighted_mass_summable μ)]
  simpa only [expectation, mul_one] using congrArg (fun x => (∑' a, (μ a).toReal * f a) - x)
    (expectation_one μ)

theorem piPMF_product_excess_summable {ι α : Type*} [Fintype ι]
    (μ : ι → PMF α) (f : ι → α → ℝ) (hf : ∀ i a, 0 ≤ f i a)
    (hs : ∀ i, Summable (fun a => (μ i a).toReal * f i a)) :
    Summable (fun x => (piPMF μ x).toReal * ((∏ i, (1 + f i (x i))) - 1)) := by
  have h := (piPMF_product_summable μ (fun i a => 1 + f i a)
    (fun i a => by linarith [hf i a]) (fun i => weighted_one_add_summable (μ i) (f i) (hs i))).sub
      (weighted_mass_summable (piPMF μ))
  simpa only [mul_sub, mul_one] using h

theorem piPMF_expectation_product_excess {ι α : Type*} [Fintype ι]
    (μ : ι → PMF α) (f : ι → α → ℝ) (hf : ∀ i a, 0 ≤ f i a)
    (hs : ∀ i, Summable (fun a => (μ i a).toReal * f i a)) :
    expectation (piPMF μ) (fun x => (∏ i, (1 + f i (x i))) - 1) =
      (∏ i, (1 + expectation (μ i) (f i))) - 1 := by
  rw [expectation_sub_one _ _ (piPMF_product_summable μ (fun i a => 1 + f i a)
    (fun i a => by linarith [hf i a]) (fun i => weighted_one_add_summable (μ i) (f i) (hs i))),
    piPMF_expectation_product μ (fun i a => 1 + f i a) (fun i a => by linarith [hf i a])]
  simp only [expectation_one_add _ _ (hs _)]

end Hindman168.DiscreteProduct
