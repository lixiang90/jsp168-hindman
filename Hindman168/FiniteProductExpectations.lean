import Hindman168.FiniteCoordinates

/-!
# Exact independent finite-product expectations

All coefficients are retained, including for signed finite masses.
Product tests factor under the actual independent coordinate law. With
each coordinate law normalized, the mean of a product excess is exactly
the product of one plus the local means, minus one.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_eq_sum {α : Type*} (μ : Mass α) (f : α → ℝ)
    {S : Finset α} (hS : μ.support ⊆ S) :
    expectation μ f = ∑ x ∈ S, μ x * f x :=
  Finsupp.sum_of_support_subset μ hS _ (by intros; exact zero_mul _)

theorem expectation_nonneg {α : Type*} (μ : Mass α) (f : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation μ f := by
  unfold expectation Finsupp.sum
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (hf x))

theorem expectation_mono {α : Type*} (μ : Mass α) (f g : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x, f x ≤ g x) : expectation μ f ≤ expectation μ g := by
  unfold expectation Finsupp.sum
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hμ x))

theorem expectation_one_add {α : Type*} (μ : Mass α) (f : α → ℝ) :
    expectation μ (fun x => 1 + f x) = total μ + expectation μ f := by
  simp only [expectation, total, Finsupp.sum, mul_add, mul_one, Finset.sum_add_distrib]

theorem expectation_sub_one {α : Type*} (μ : Mass α) (f : α → ℝ) :
    expectation μ (fun x => f x - 1) = expectation μ f - total μ := by
  simp only [expectation, total, Finsupp.sum, mul_sub, mul_one, Finset.sum_sub_distrib]

theorem expectation_piMass_product {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (f : ∀ i, α i → ℝ) :
    expectation (piMass μ) (fun x => ∏ i, f i (x i)) = ∏ i, expectation (μ i) (f i) := by
  classical
  rw [expectation_eq_sum _ _ (piMass_support μ)]
  simp only [piMass_apply]
  simp_rw [← Finset.prod_mul_distrib]
  unfold expectation Finsupp.sum
  exact (Finset.prod_univ_sum (fun i => (μ i).support) (fun i x => μ i x * f i x)).symm

theorem expectation_piMass_product_excess {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (ht : ∀ i, total (μ i) = 1) (f : ∀ i, α i → ℝ) :
    expectation (piMass μ) (fun x => (∏ i, (1 + f i (x i))) - 1) =
      (∏ i, (1 + expectation (μ i) (f i))) - 1 := by
  rw [expectation_sub_one, expectation_piMass_product μ (fun i x => 1 + f i x), piMass_total_one μ ht]
  simp only [expectation_one_add, ht]

end Hindman168.FiniteMass
