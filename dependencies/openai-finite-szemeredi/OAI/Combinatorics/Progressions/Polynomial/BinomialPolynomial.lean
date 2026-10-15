import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer

/-
Compatibility lemma copied from Mathlib/Combinatorics/Enumerative/Stirling.lean,
mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612.
Copyright (c) 2025 Beibei Xiong. Released under Apache 2.0.
Authors: Beibei Xiong, Yu Shao, Weijie Jiang, Zhengfeng Yang.
The fixed local mathlib revision predates this identity.
-/
namespace Nat

private theorem descFactorial_mul_self_compat (n k : ℕ) :
    n.descFactorial k * n = n.descFactorial (k + 1) + k * n.descFactorial k := by
  by_cases hk : k ≤ n
  · rw [descFactorial_succ, ← add_mul, Nat.sub_add_cancel hk, mul_comm]
  · have hzero : n.descFactorial k = 0 :=
      descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hk)
    have hzero' : n.descFactorial (k + 1) = 0 :=
      descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp only [hzero, hzero', zero_mul, mul_zero, add_zero]

/-- Every power `n ^ k` is a linear combination of the descending factorials `n.descFactorial j`
with the Stirling numbers of the second kind `stirlingSecond k j` as coefficients. -/
theorem pow_eq_sum_stirlingSecond_mul_descFactorial (n k : ℕ) :
    n ^ k = ∑ j ∈ Finset.range (k + 1), stirlingSecond k j * n.descFactorial j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : ∑ j ∈ Finset.range (k + 1), stirlingSecond k j * (j * n.descFactorial j)
        = ∑ j ∈ Finset.range (k + 1),
            (j + 1) * (stirlingSecond k (j + 1) * n.descFactorial (j + 1)) := by
      rw [Finset.sum_range_succ' (fun j ↦ stirlingSecond k j * (j * n.descFactorial j)) k,
        Finset.sum_range_succ (fun j ↦ (j + 1) * (stirlingSecond k (j + 1) *
          n.descFactorial (j + 1))) k,
        stirlingSecond_eq_zero_of_lt k.lt_add_one]
      simp [mul_left_comm]
    rw [pow_succ, ih, Finset.sum_mul,
      Finset.sum_range_succ' (fun j ↦ stirlingSecond (k + 1) j * n.descFactorial j) (k + 1)]
    simp only [mul_assoc, descFactorial_mul_self_compat, mul_add, Finset.sum_add_distrib, this,
      stirlingSecond_succ_succ, add_mul, stirlingSecond_succ_zero, zero_mul, add_zero]
    exact add_comm _ _


end Nat

namespace OAI

section

namespace Erdos3

open Polynomial

noncomputable def binomialPolynomial (n : ℕ) : Polynomial ℚ :=
  (n.factorial : ℚ)⁻¹ • descPochhammer ℚ n

@[simp] theorem binomialPolynomial_zero : binomialPolynomial 0 = 1 := by
  simp [binomialPolynomial]

theorem factorial_smul_binomialPolynomial (n : ℕ) :
    (n.factorial : ℚ) • binomialPolynomial n = descPochhammer ℚ n := by
  rw [binomialPolynomial, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast n.factorial_ne_zero

theorem binomialPolynomial_natDegree (n : ℕ) : (binomialPolynomial n).natDegree = n := by
  rw [binomialPolynomial, natDegree_smul]
  · exact descPochhammer_natDegree ℚ n
  · exact inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)

theorem binomialPolynomial_eval_nat (n a : ℕ) :
    (binomialPolynomial n).eval (a : ℚ) = (a.choose n : ℚ) := by
  rw [binomialPolynomial, smul_eq_C_mul, eval_mul, eval_C,
    Nat.cast_choose_eq_descPochhammer_div ℚ a n]
  simp only [div_eq_mul_inv, mul_comm]

theorem X_pow_eq_sum_binomialPolynomial (n : ℕ) :
    (X : Polynomial ℚ) ^ n =
      ∑ k ∈ Finset.range (n + 1), ((Nat.stirlingSecond n k * k.factorial : ℕ) : ℚ) •
        binomialPolynomial k := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun a : ℕ => (a : ℚ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hinf.mono
  rintro _ ⟨a, rfl⟩
  change eval (a : ℚ) ((X : Polynomial ℚ) ^ n) = _
  simp only [eval_pow, eval_X, eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C,
    binomialPolynomial_eval_nat, Nat.cast_mul]
  have h := congrArg (fun b : ℕ => (b : ℚ)) (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial a n)
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul,
    Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] using h

end Erdos3

end

end OAI
