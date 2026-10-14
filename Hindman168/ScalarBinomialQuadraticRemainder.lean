import Hindman168.ScalarBinomialCoefficientModOne
import Hindman168.ScalarPolynomialTopRemoval

/-! The TRUE paper quadratic coefficient differs from 2*Q_2 only by
bounded higher terms; no bound on Q_2 itself is assumed. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_binomial_coefficient_sub (P Q : ℝ[X]) (D i : ℕ) :
    scalarPolynomialBinomialCoefficient (P-Q) D i =
      scalarPolynomialBinomialCoefficient P D i-scalarPolynomialBinomialCoefficient Q D i := by
  simp only [scalarPolynomialBinomialCoefficient,coeff_sub,sub_mul,Finset.sum_sub_distrib,mul_sub]

theorem scalar_binomial_quadratic_monomial (x : ℝ) (D : ℕ) (hD : 2 ≤ D) :
    scalarPolynomialBinomialCoefficient (monomial 2 x) D 2 = 2*x := by
  unfold scalarPolynomialBinomialCoefficient
  simp only [coeff_monomial,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  have hm : 2 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  norm_num [Nat.stirlingSecond_self]

theorem scalar_binomial_quadratic_drop (Q : ℝ[X]) (D : ℕ) (hD : 2 ≤ D) :
    scalarPolynomialBinomialCoefficient (scalarPolynomialDropTop Q 2) D 2 =
      scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2 := by
  rw [scalarPolynomialDropTop,scalar_binomial_coefficient_sub,
    scalar_binomial_quadratic_monomial _ D hD]

theorem scalar_binomial_quadratic_remainder_bound (Q : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hD : 2 ≤ D) (hN : 0 < N) (hB : 0 ≤ B)
    (hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)^2*‖(((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) : ℝ) :
      UnitAddCircle)‖ ≤ (scalarBinomialCoefficientBudget D : ℝ)*B := by
  have hDrop : ∀ j : ℕ, 2 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*(scalarPolynomialDropTop Q 2).coeff j : ℝ) : UnitAddCircle)‖ ≤ B := by
    intro j hj hjD
    rw [scalarPolynomialDropTop,coeff_sub,coeff_monomial]
    by_cases he : 2=j
    · rw [if_pos he,← he,sub_self,mul_zero,AddCircle.coe_zero,norm_zero,mul_zero]
      exact hB
    · rw [if_neg he,sub_zero]
      exact hHigher j (by omega) hjD
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he := scalar_binomial_coefficient_mod_one (scalarPolynomialDropTop Q 2) D M 2 2
    hD le_rfl (N : ℝ) B hNr hB hDrop
  rwa [scalar_binomial_quadratic_drop Q D hD] at he

end Hindman168
