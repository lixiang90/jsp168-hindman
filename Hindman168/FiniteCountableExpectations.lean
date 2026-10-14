import Hindman168.CountableExpectations
import Hindman168.FiniteProductExpectations
import Hindman168.UnitCRTJointLaw

/-!
# Exact finite and countable expectation bridges

The finite masses and their PMFs have the same original coefficients.
Every test on a finite mass is summable, including signed tests. Fubini
and support-restricted inequalities retain the original finite weights.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem toPMF_weighted_summable {α : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) (f : α → ℝ) :
    Summable (fun a => (toPMF μ hμ ht a).toReal * f a) := by
  apply summable_of_ne_finset_zero (s := μ.support)
  intro a ha
  rw [toPMF_apply, Finsupp.notMem_support_iff.mp ha, ENNReal.ofReal_zero,
    ENNReal.toReal_zero, zero_mul]

theorem toPMF_expectation {α : Type*} (μ : Mass α) (hμ : ∀ a, 0 ≤ μ a)
    (ht : total μ = 1) (f : α → ℝ) :
    DiscreteProduct.expectation (toPMF μ hμ ht) f = expectation μ f := by
  unfold DiscreteProduct.expectation
  rw [tsum_eq_sum (s := μ.support) (fun a ha => by
    rw [toPMF_apply, Finsupp.notMem_support_iff.mp ha, ENNReal.ofReal_zero,
      ENNReal.toReal_zero, zero_mul])]
  simp only [toPMF_apply, ENNReal.toReal_ofReal (hμ _)]
  rfl

theorem toPMF_piMass {ι α : Type*} [Fintype ι] (μ : ι → Mass α)
    (hμ : ∀ i a, 0 ≤ μ i a) (ht : ∀ i, total (μ i) = 1) :
    toPMF (piMass μ) (piMass_nonneg μ hμ) (piMass_total_one μ ht) =
      DiscreteProduct.piPMF (fun i => toPMF (μ i) (hμ i) (ht i)) := by
  ext x
  rw [toPMF_apply, piMass_apply, DiscreteProduct.piPMF_apply]
  simp only [toPMF_apply]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hμ i (x i))

theorem expectation_tensor {α β : Type*} (μ : Mass α) (ν : Mass β)
    (f : α × β → ℝ) :
    expectation (tensor μ ν) f = expectation μ (fun a => expectation ν (fun b => f (a,b))) := by
  rw [expectation_eq_sum _ _ (tensor_support μ ν), Finset.sum_product]
  simp only [tensor_apply, expectation, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expectation_mono_support {α : Type*} (μ : Mass α) (f g : α → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hfg : ∀ a ∈ μ.support, f a ≤ g a) :
    expectation μ f ≤ expectation μ g := by
  unfold expectation Finsupp.sum
  exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hfg a ha) (hμ a))

theorem expectation_const {α : Type*} (μ : Mass α) (c : ℝ) :
    expectation μ (fun _ => c) = total μ * c := by
  simp only [expectation, total, Finsupp.sum, Finset.sum_mul]

theorem expectation_add_const {α : Type*} (μ : Mass α) (f : α → ℝ) (c : ℝ) :
    expectation μ (fun a => f a + c) = expectation μ f + total μ * c := by
  simp only [expectation, total, Finsupp.sum, mul_add, Finset.sum_add_distrib, Finset.sum_mul]

end Hindman168.FiniteMass
