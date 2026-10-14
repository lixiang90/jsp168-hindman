import Hindman168.RoughBinomialDenominator
import Hindman168.ScalarPolynomialStirlingExpansion

namespace Hindman168
open scoped BigOperators Classical

noncomputable def mvBinomialBox (κ : Type*) [Fintype κ] (D : ℕ) : Finset (κ → ℕ) :=
  Fintype.piFinset (fun _ : κ => Finset.range (D+1))

theorem mv_binomial_box_mem {κ : Type*} [Fintype κ] (D : ℕ) (I : κ → ℕ) :
    I ∈ mvBinomialBox κ D ↔ ∀ j, I j ≤ D := by
  simp only [mvBinomialBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

theorem mv_binomial_box_mem_of_weight_le {κ : Type*} [Fintype κ]
    (D : ℕ) (I : κ → ℕ) (hI : (∑ j, I j) ≤ D) : I ∈ mvBinomialBox κ D := by
  apply (mv_binomial_box_mem D I).mpr
  intro j
  exact (Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)).trans hI

def mvBinomialStirlingWeight {κ : Type*} [Fintype κ] (I J : κ → ℕ) : ℕ :=
  ∏ j, (I j).factorial*Nat.stirlingSecond (J j) (I j)

noncomputable def mvPolynomialBinomialCoefficient {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (D : ℕ) (I : κ → ℕ) : ℝ :=
  ∑ J ∈ mvBinomialBox κ D,
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p*(mvBinomialStirlingWeight I J : ℝ)

theorem mv_binomial_stirling_weight_zero_below {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (j : κ) (hj : J j < I j) : mvBinomialStirlingWeight I J = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [Nat.stirlingSecond_eq_zero_of_lt hj, mul_zero]

theorem mv_binomial_stirling_weight_weight_le {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (h : mvBinomialStirlingWeight I J ≠ 0) : (∑ j, I j) ≤ ∑ j, J j := by
  apply Finset.sum_le_sum
  intro j _
  by_contra! hj
  exact h (mv_binomial_stirling_weight_zero_below I J j hj)

theorem mv_binomial_stirling_weight_zero_of_weight_lt {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (h : (∑ j, J j) < ∑ j, I j) : mvBinomialStirlingWeight I J = 0 := by
  by_contra hz
  exact (not_lt_of_ge (mv_binomial_stirling_weight_weight_le I J hz)) h

end Hindman168
