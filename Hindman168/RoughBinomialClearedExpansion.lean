import Hindman168.RoughBinomialTriangularCoefficients

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_binomial_cleared_expansion {κ : Type*} [Fintype κ]
    (q : ℕ) (s : Finset (κ → ℕ)) (α : (κ → ℕ) → ℝ) (c : ℝ)
    (hJ : ∀ J ∈ s, ∀ j, J j ≤ q) :
    C ((q.factorial : ℝ)^(Fintype.card κ))*
      (C c+∑ J ∈ s, C (α J)*roughMvBinomialPolynomial J) =
    C (((q.factorial : ℝ)^(Fintype.card κ))*c)+
      ∑ J ∈ s, C (α J)*map (Int.castRingHom ℝ) (roughMvClearedBinomialPolynomial q J) := by
  rw [mul_add, Finset.mul_sum, ← map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJs
  rw [← rough_mv_binomial_denominator q J (hJ J hJs)]
  ring

theorem rough_binomial_cleared_positive_coefficient {κ : Type*} [Fintype κ]
    (q : ℕ) (s : Finset (κ → ℕ)) (α : (κ → ℕ) → ℝ) (c : ℝ)
    (hJ : ∀ J ∈ s, ∀ j, J j ≤ q) (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ((q.factorial : ℝ)^(Fintype.card κ))*
      coeff (Finsupp.equivFunOnFinite.symm I)
        (C c+∑ J ∈ s, C (α J)*roughMvBinomialPolynomial J) =
      ∑ J ∈ s,
        ((coeff (Finsupp.equivFunOnFinite.symm I) (roughMvClearedBinomialPolynomial q J) : ℤ) : ℝ)*α J := by
  have hzero : Finsupp.equivFunOnFinite.symm I ≠ 0 := by
    intro hz
    have hj : ∀ j, I j = 0 := fun j => by
      simpa using congrArg (fun f : κ →₀ ℕ => f j) hz
    simp only [hj, Finset.sum_const_zero] at hI
    omega
  have h := congrArg (coeff (Finsupp.equivFunOnFinite.symm I))
    (rough_binomial_cleared_expansion q s α c hJ)
  simp only [coeff_C_mul, coeff_add, coeff_C, if_neg (Ne.symm hzero), zero_add,
    coeff_sum, coeff_map, Int.coe_castRingHom] at h
  simp only [coeff_add, coeff_C, if_neg (Ne.symm hzero), zero_add,
    coeff_sum, coeff_C_mul]
  exact h.trans (Finset.sum_congr rfl (fun J _ => mul_comm _ _))

end Hindman168
