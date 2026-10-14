import Hindman168.MvBinomialCoefficientModOne

/-! ALL positive monomial bounds give ALL positive binomial bounds at the
same original scale. Multiindices outside the actual degree box are handled
explicitly by zero integer Stirling weights. -/
namespace Hindman168
open scoped BigOperators Classical

theorem mv_complete_binomial_transfer {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (d N : ℕ) (A : ℝ) (hN : 0 < N) (hA : 0 ≤ A)
    (hMono : ∀ J : κ → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ A) :
    ∀ I : κ → ℕ, 0 < (∑ i, I i) →
      (N : ℝ)^(∑ i, I i)*‖((mvPolynomialBinomialCoefficient p d I : ℝ) : UnitAddCircle)‖ ≤
        (mvBinomialCoefficientBudget κ d : ℝ)*A := by
  intro I hI
  by_cases hi : I ∈ mvBinomialBox κ d
  · have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h := mv_binomial_coefficient_mod_one p d 1 1 I hi hI (N : ℝ) A hn hA
      (fun J _ hJ => by simpa only [Nat.cast_one,one_mul] using hMono J hJ)
    simpa only [Nat.cast_one,one_mul] using h
  · have hNot : ¬ ∀ i, I i ≤ d := by
      intro h
      exact hi ((mv_binomial_box_mem d I).mpr h)
    push Not at hNot
    obtain ⟨i,hdi⟩ := hNot
    have hz : mvPolynomialBinomialCoefficient p d I=0 := by
      unfold mvPolynomialBinomialCoefficient
      apply Finset.sum_eq_zero
      intro J hJ
      rw [mv_binomial_stirling_weight_zero_below I J i
        (((mv_binomial_box_mem d J).mp hJ i).trans_lt hdi),Nat.cast_zero,mul_zero]
    rw [hz,AddCircle.coe_zero,norm_zero,mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hA

end Hindman168
