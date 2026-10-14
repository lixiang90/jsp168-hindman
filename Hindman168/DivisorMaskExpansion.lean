import Hindman168.IntegerProductLaw
import Hindman168.FiniteCountableExpectations
import Hindman168.EventMass

/-!
# Independent integer divisor-mask expansion

The product of the original masks is exactly the weighted expectation
of the simultaneous divisibility event under the original independent
divisor law. Finite Fubini then integrates the base law without changing
any coefficient. Integers of either sign are allowed.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_comm {α β : Type*} (μ : Mass α) (ν : Mass β)
    (f : α → β → ℝ) :
    expectation μ (fun a => expectation ν (f a)) =
      expectation ν (fun b => expectation μ (fun a => f a b)) := by
  simp only [expectation, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expectation_const_mul {α : Type*} (μ : Mass α) (c : ℝ) (f : α → ℝ) :
    expectation μ (fun a => c * f a) = c * expectation μ f := by
  simp only [expectation, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expectation_indicator {α : Type*} (μ : Mass α) (E : α → Prop) :
    expectation μ (fun a => if E a then 1 else 0) = event μ E := by
  simp only [expectation, event, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem integerDivisorMask_expectation (ρ : Mass ℕ) (z : ℤ) :
    integerDivisorMask ρ z = expectation ρ (fun k => if (k : ℤ) ∣ z then (k : ℝ) else 0) := rfl

theorem divisor_indicator_product {ι : Type*} [Fintype ι] (k : ι → ℕ) (z : ι → ℤ) :
    (∏ i, if (k i : ℤ) ∣ z i then (k i : ℝ) else 0) =
      ((∏ i, k i : ℕ) : ℝ) * (if ∀ i, (k i : ℤ) ∣ z i then 1 else 0) := by
  by_cases h : ∀ i, (k i : ℤ) ∣ z i
  · simp only [if_pos h, mul_one, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => if_pos (h i))
  · rw [if_neg h, mul_zero]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integerDivisorMask_product {ι : Type*} [Fintype ι]
    (ρ : ι → Mass ℕ) (z : ι → ℤ) :
    (∏ i, integerDivisorMask (ρ i) (z i)) = expectation (piMass ρ)
      (fun k => ((∏ i, k i : ℕ) : ℝ) * (if ∀ i, (k i : ℤ) ∣ z i then 1 else 0)) := by
  have h := expectation_piMass_product ρ (fun i k => if (k : ℤ) ∣ z i then (k : ℝ) else 0)
  simp only [← integerDivisorMask_expectation, divisor_indicator_product] at h
  exact h.symm

theorem integerDivisorMask_product_expectation {ι α : Type*} [Fintype ι]
    (ρ : ι → Mass ℕ) (μ : Mass α) (z : α → ι → ℤ) :
    expectation μ (fun x => ∏ i, integerDivisorMask (ρ i) (z x i)) =
      expectation (piMass ρ) (fun k => ((∏ i, k i : ℕ) : ℝ) *
        event μ (fun x => ∀ i, (k i : ℤ) ∣ z x i)) := by
  simp_rw [integerDivisorMask_product]
  rw [expectation_comm μ (piMass ρ)]
  congr 1
  funext k
  rw [expectation_const_mul]
  congr 1
  simp only [expectation, event, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem restricted_integerDivisorMask_product_expectation {ι α : Type*} [Fintype ι]
    (ρ : ι → Mass ℕ) (μ : Mass α) (z : α → ι → ℤ) (E : α → Prop) :
    expectation μ (fun x => if E x then ∏ i, integerDivisorMask (ρ i) (z x i) else 0) =
      expectation (piMass ρ) (fun k => ((∏ i, k i : ℕ) : ℝ) *
        event μ (fun x => E x ∧ ∀ i, (k i : ℤ) ∣ z x i)) := by
  have hpoint (x : α) :
      (if E x then ∏ i, integerDivisorMask (ρ i) (z x i) else 0) =
        expectation (piMass ρ) (fun k => ((∏ i, k i : ℕ) : ℝ) *
          (if E x ∧ ∀ i, (k i : ℤ) ∣ z x i then 1 else 0)) := by
    by_cases hx : E x
    · simp only [hx, true_and]
      exact integerDivisorMask_product ρ (z x)
    · simp only [hx, false_and, if_false, mul_zero, expectation, Finsupp.sum_fun_zero]
  simp_rw [hpoint]
  rw [expectation_comm μ (piMass ρ)]
  congr 1
  funext k
  rw [expectation_const_mul]
  congr 1
  simp only [expectation, event, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

end Hindman168
