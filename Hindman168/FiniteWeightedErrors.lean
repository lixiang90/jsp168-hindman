import Hindman168.FiniteCountableExpectations
import Hindman168.FiniteEventComparison

/-!
# Weighted errors under original finite laws

Bounds may hold only on the actual support. Averaging retains its
original total mass; a prime-only restriction retains its original
event mass, with no division by that mass.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_add {α : Type*} (μ : Mass α) (f g : α → ℝ) :
    expectation μ (fun a => f a + g a) = expectation μ f + expectation μ g := by
  simp only [expectation, Finsupp.sum, mul_add, Finset.sum_add_distrib]

theorem expectation_sub {α : Type*} (μ : Mass α) (f g : α → ℝ) :
    expectation μ (fun a => f a - g a) = expectation μ f - expectation μ g := by
  simp only [expectation, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

theorem expectation_nonneg_support {α : Type*} (μ : Mass α) (f : α → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hf : ∀ a ∈ μ.support, 0 ≤ f a) : 0 ≤ expectation μ f := by
  unfold expectation Finsupp.sum
  exact Finset.sum_nonneg (fun a ha => mul_nonneg (hμ a) (hf a ha))

theorem expectation_difference_support_bound {α : Type*} (μ : Mass α)
    (hμ : ∀ a, 0 ≤ μ a) (f g : α → ℝ) (B : ℝ)
    (hf : ∀ a ∈ μ.support, |f a - g a| ≤ B) :
    |expectation μ f - expectation μ g| ≤ total μ * B := by
  rw [← expectation_sub]
  unfold expectation
  rw [Finsupp.sum]
  calc
    _ ≤ ∑ a ∈ μ.support, |μ a * (f a - g a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ μ.support, μ a * B := Finset.sum_le_sum (fun a ha => by
      rw [abs_mul, abs_of_nonneg (hμ a)]
      exact mul_le_mul_of_nonneg_left (hf a ha) (hμ a))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem expectation_congr_support {α : Type*} (μ : Mass α) (f g : α → ℝ)
    (hfg : ∀ a ∈ μ.support, f a = g a) : expectation μ f = expectation μ g := by
  unfold expectation Finsupp.sum
  apply Finset.sum_congr rfl
  intro a ha
  change μ a * f a = μ a * g a
  rw [hfg a ha]

theorem restricted_expectation_sub_event {α : Type*} (μ : Mass α) (E : α → Prop)
    (f : α → ℝ) :
    expectation μ (fun a => if E a then f a else 0) - event μ E =
      expectation μ (fun a => if E a then f a - 1 else 0) := by
  simp only [expectation, event, Finsupp.sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

end Hindman168.FiniteMass
