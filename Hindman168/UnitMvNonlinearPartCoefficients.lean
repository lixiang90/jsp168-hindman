import Hindman168.NativeRationalFunctionalScalarPolynomial
import Hindman168.ScalarUnitPolynomial
import Hindman168.ScalarPolynomialBinomialExpansion

/-! Exact coefficients of the ACTUAL removed nonlinear scalar polynomial;
constant/linear monomials vanish and EVERY higher coefficient is retained. -/
namespace Hindman168
open Polynomial
open scoped Classical

theorem unit_mv_nonlinear_part_zero_coefficient (P : MvPolynomial Unit ℝ) :
    (scalarUnitPolynomial (unitMvNonlinearPart P)).coeff 0=0 := by
  simp [scalar_unit_polynomial_coefficient,unitMvNonlinearPart,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X]

theorem unit_mv_nonlinear_part_one_coefficient (P : MvPolynomial Unit ℝ) :
    (scalarUnitPolynomial (unitMvNonlinearPart P)).coeff 1=0 := by
  have h0 : (0 : Unit →₀ ℕ) ≠ Finsupp.single () 1 := by
    intro he
    have hz : 0=1 := by simpa using congrArg (fun J : Unit →₀ ℕ => J ()) he
    omega
  simp [scalar_unit_polynomial_coefficient,unitMvNonlinearPart,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,h0]

theorem unit_mv_nonlinear_part_high_coefficient (P : MvPolynomial Unit ℝ) (j : ℕ) (hj : 2 ≤ j) :
    (scalarUnitPolynomial (unitMvNonlinearPart P)).coeff j=(scalarUnitPolynomial P).coeff j := by
  have hJ0 : (0 : Unit →₀ ℕ) ≠ Finsupp.single () j := by
    intro he
    have hz : 0=j := by simpa using congrArg (fun J : Unit →₀ ℕ => J ()) he
    omega
  have hJ1 : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ Finsupp.single () j := by
    intro he
    have hz : 1=j := by simpa using congrArg (fun J : Unit →₀ ℕ => J ()) he
    omega
  rw [scalar_unit_polynomial_coefficient,scalar_unit_polynomial_coefficient]
  simp only [unitMvNonlinearPart,MvPolynomial.coeff_sub,MvPolynomial.coeff_C,
    MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X,if_neg hJ0,if_neg hJ1,mul_zero,sub_zero]

theorem scalar_binomial_high_coefficient_congr (P Q : ℝ[X])
    (hPQ : ∀ j : ℕ, 2 ≤ j → P.coeff j=Q.coeff j) (D i : ℕ) (hi : 2 ≤ i) :
    scalarPolynomialBinomialCoefficient P D i=scalarPolynomialBinomialCoefficient Q D i := by
  unfold scalarPolynomialBinomialCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 2 ≤ j
  · rw [hPQ j hj]
  · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : j < i),Nat.cast_zero,mul_zero,mul_zero]

end Hindman168
