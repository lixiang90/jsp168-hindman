import Hindman168.RoughBinomialDenominator

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_mv_falling_degreeOf {κ R : Type*} [Fintype κ]
    [CommRing R] [Nontrivial R] (J : κ → ℕ) (i : κ) :
    (roughMvFallingPolynomial J : MvPolynomial κ R).degreeOf i ≤ J i := by
  have hf : ∀ j k, (X j-C (k : R) : MvPolynomial κ R).degreeOf i ≤
      if i = j then 1 else 0 := fun j k => by
    have h := degreeOf_sub_le i (X j : MvPolynomial κ R) (C (k : R))
    simpa only [degreeOf_X, degreeOf_C, max_zero] using h
  calc
    _ ≤ ∑ j, (∏ k ∈ Finset.range (J j), (X j-C (k : R))).degreeOf i :=
      degreeOf_prod_le _ _ _
    _ ≤ ∑ j, ∑ k ∈ Finset.range (J j), (X j-C (k : R) : MvPolynomial κ R).degreeOf i := by
      apply Finset.sum_le_sum
      intro j _
      exact degreeOf_prod_le _ _ _
    _ ≤ ∑ j, ∑ _k ∈ Finset.range (J j), if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun k _ => hf j k)
    _ = J i := by simp [Finset.sum_ite_eq]

theorem rough_mv_cleared_binomial_degreeOf {κ : Type*} [Fintype κ]
    (q : ℕ) (J : κ → ℕ) (i : κ) :
    (roughMvClearedBinomialPolynomial q J).degreeOf i ≤ J i := by
  unfold roughMvClearedBinomialPolynomial
  rw [← map_prod]
  exact (degreeOf_C_mul_le _ _ _).trans (rough_mv_falling_degreeOf J i)

theorem rough_mv_cleared_binomial_coeff_zero {κ : Type*} [Fintype κ]
    (q : ℕ) (I J : κ → ℕ) (h : ¬ ∀ j, I j ≤ J j) :
    coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  apply notMem_support_iff.mp
  apply notMem_support_of_degreeOf_lt i
  simpa only [Finsupp.coe_equivFunOnFinite_symm] using
    (rough_mv_cleared_binomial_degreeOf q J i).trans_lt hi

end Hindman168
