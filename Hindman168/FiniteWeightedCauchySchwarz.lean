import Hindman168.FiniteWeightedErrors
import Hindman168.DivisorMaskExpansion
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The exact weighted Cauchy--Schwarz duplication step

The outside law retains its original nonnegative finite coefficients.
The density is required only to dominate the outside factor on actual
support. No division by that density or event mass is used. The inside
law may depend on every outside parameter; its two copies are independent
conditional on those parameters, with the same original coefficients.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem finite_weighted_cauchy_schwarz {α : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (H Ω g : α → ℝ)
    (hbound : ∀ x ∈ μ.support, |H x| ≤ Ω x) :
    |expectation μ (fun x => H x * g x)| ^ 2 ≤
      expectation μ Ω * expectation μ (fun x => Ω x * (g x) ^ 2) := by
  have hΩ (x : α) (hx : x ∈ μ.support) : 0 ≤ Ω x :=
    (abs_nonneg (H x)).trans (hbound x hx)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul μ.support
    (r := fun x => μ x * (H x * g x))
    (f := fun x => μ x * Ω x) (g := fun x => μ x * (Ω x * (g x) ^ 2))
    (fun x hx => mul_nonneg (hμ x) (hΩ x hx))
    (fun x hx => mul_nonneg (hμ x) (mul_nonneg (hΩ x hx) (sq_nonneg _)))
    (fun x hx => by
      have hf2 : (H x) ^ 2 ≤ (Ω x) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (H x)) (hΩ x hx)).mpr (hbound x hx)
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf2 (sq_nonneg (μ x))) (sq_nonneg (g x))
      convert hm using 1 <;> ring)
  simpa only [expectation, Finsupp.sum, sq_abs] using hc

theorem expectation_tensor_product {α β : Type*} (μ : Mass α) (ν : Mass β)
    (f : α → ℝ) (g : β → ℝ) :
    expectation (tensor μ ν) (fun ab => f ab.1 * g ab.2) = expectation μ f * expectation ν g := by
  rw [expectation_tensor]
  simp_rw [expectation_const_mul]
  unfold expectation Finsupp.sum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expectation_independent_square {α : Type*} (μ : Mass α) (f : α → ℝ) :
    expectation (tensor μ μ) (fun ab => f ab.1 * f ab.2) = (expectation μ f) ^ 2 := by
  rw [expectation_tensor_product]
  ring

theorem conditional_weighted_cauchy_schwarz {α β : Type*} (μ : Mass α)
    (hμ : ∀ x, 0 ≤ μ x) (ν : α → Mass β) (H Ω : α → ℝ) (g : α → β → ℝ)
    (hbound : ∀ x ∈ μ.support, |H x| ≤ Ω x) :
    |expectation μ (fun x => H x * expectation (ν x) (g x))| ^ 2 ≤
      expectation μ Ω * expectation μ (fun x => expectation (tensor (ν x) (ν x))
        (fun ab => Ω x * g x ab.1 * g x ab.2)) := by
  have he (x : α) : expectation (tensor (ν x) (ν x))
      (fun ab => Ω x * g x ab.1 * g x ab.2) = Ω x * (expectation (ν x) (g x)) ^ 2 := by
    calc
      _ = Ω x * expectation (tensor (ν x) (ν x)) (fun ab => g x ab.1 * g x ab.2) := by
        rw [← expectation_const_mul]
        congr 1
        funext ab
        ring
      _ = _ := by rw [expectation_independent_square]
  simpa only [he] using finite_weighted_cauchy_schwarz μ hμ H Ω
    (fun x => expectation (ν x) (g x)) hbound


theorem product_conditional_weighted_cauchy_schwarz {α β ι : Type*}
    (μ : Mass α) (hμ : ∀ x, 0 ≤ μ x) (ν : α → Mass β) (U : Finset ι)
    (H Ω : ι → α → ℝ) (g : α → β → ℝ)
    (hbound : ∀ x ∈ μ.support, ∀ i ∈ U, |H i x| ≤ Ω i x) :
    |expectation μ (fun x => (∏ i ∈ U, H i x) * expectation (ν x) (g x))| ^ 2 ≤
      expectation μ (fun x => ∏ i ∈ U, Ω i x) *
        expectation μ (fun x => expectation (tensor (ν x) (ν x))
          (fun ab => (∏ i ∈ U, Ω i x) * g x ab.1 * g x ab.2)) := by
  apply conditional_weighted_cauchy_schwarz μ hμ ν
    (fun x => ∏ i ∈ U, H i x) (fun x => ∏ i ∈ U, Ω i x) g
  intro x hx
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg (H i x)) (hbound x hx)

end Hindman168.FiniteMass
