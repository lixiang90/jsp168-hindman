import Hindman168.ScalarDifferenceDiagonalRecovery
import Hindman168.ScalarPolynomialValueOneRemainder
import Hindman168.ScalarBinomialQuadraticRemainder

/-! Actual paper beta=P(1) and alpha=the SECOND BINOMIAL coefficient of Q.
Both changes from ordinary coefficients are bounded at the original scale. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_difference_paper_linear_relation_bound (P Q : ℝ[X]) (D M h N : ℕ)
    (A B C : ℝ) (hP : P.natDegree ≤ D) (hQ : Q.natDegree ≤ D) (hD : 2 ≤ D)
    (hZero : P.eval 0=0) (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B) (hC : 0 ≤ C) (σ : ℝ)
    (hR : (N : ℝ)*‖((scalarDifferencePolynomial P Q h σ).coeff 1 : UnitAddCircle)‖ ≤ A)
    (hHigherQ : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B)
    (hHigherP : ∀ j : ℕ, 2 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*P.coeff j : ℝ) : UnitAddCircle)‖ ≤ C) :
    (N : ℝ)*‖(((M : ℝ)*(P.eval 1+scalarPolynomialBinomialCoefficient Q D 2*(h : ℝ)+σ) : ℝ) :
      UnitAddCircle)‖ ≤ (M : ℝ)*A+(scalarTaylorTailBudget D : ℝ)*B+(D+1 : ℕ)*C+
        (scalarBinomialCoefficientBudget D : ℝ)*B := by
  let x : ℝ := (M : ℝ)*(P.coeff 1+2*Q.coeff 2*(h : ℝ)+σ)
  let y : ℝ := (M : ℝ)*(P.eval 1-P.coeff 1)
  let z : ℝ := (h : ℝ)*((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2))
  have hx := scalar_difference_linear_residual_bound P Q D M h N A B hQ hD hN hh hB σ hR hHigherQ
  have hy := scalar_polynomial_value_one_remainder_bound P D M N C hP (by omega) hZero hN hC hHigherP
  have hz : (N : ℝ)*‖(z : UnitAddCircle)‖ ≤ (scalarBinomialCoefficientBudget D : ℝ)*B := by
    have hm := mod_one_natural_multiplier_norm_le h ((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2))
    have hNum : (N : ℝ)*(h : ℝ) ≤ (N : ℝ)^2 := by
      have hhR : (h : ℝ) ≤ N := by exact_mod_cast hh
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    calc
      _ ≤ (N : ℝ)*((h : ℝ)*‖(((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) : ℝ) :
          UnitAddCircle)‖) := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg N)
      _ = ((N : ℝ)*(h : ℝ))*‖(((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) : ℝ) :
          UnitAddCircle)‖ := by ring
      _ ≤ (N : ℝ)^2*‖(((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) : ℝ) :
          UnitAddCircle)‖ := mul_le_mul_of_nonneg_right hNum (norm_nonneg _)
      _ ≤ _ := scalar_binomial_quadratic_remainder_bound Q D M N B hD hN hB hHigherQ
  have he : (M : ℝ)*(P.eval 1+scalarPolynomialBinomialCoefficient Q D 2*(h : ℝ)+σ) = x+y+z := by
    dsimp [x,y,z]
    ring
  rw [he,AddCircle.coe_add,AddCircle.coe_add]
  have ht : ‖(x : UnitAddCircle)+(y : UnitAddCircle)+(z : UnitAddCircle)‖ ≤
      ‖(x : UnitAddCircle)‖+‖(y : UnitAddCircle)‖+‖(z : UnitAddCircle)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hmul := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α := ℝ) N)
  rw [mul_add,mul_add] at hmul
  exact hmul.trans (add_le_add (add_le_add hx hy) hz)

end Hindman168
