import Hindman168.ScalarBinomialQuadraticRemainder
import Hindman168.ModOneNaturalMultiplier

/-! ACTUAL paper second-binomial bound plus true higher monomial bounds
give COMPLETE nonlinear monomial/binomial tables after multiplying by TWO.
The missing quadratic monomial is proved small, not assumed. -/
namespace Hindman168
open Polynomial
open scoped BigOperators

theorem scalar_quadratic_complete_monomial_bound (Q : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hD : 2 ≤ D) (hN : 0 < N) (hB : 0 ≤ B)
    (hSecond : (N : ℝ)^2*‖(((M : ℝ)*scalarPolynomialBinomialCoefficient Q D 2 : ℝ) : UnitAddCircle)‖ ≤ B)
    (hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ D → (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∀ j : ℕ, 2 ≤ j → j ≤ D → (N : ℝ)^j*‖((((2*M : ℕ) : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤
      (2+(scalarBinomialCoefficientBudget D : ℝ))*B := by
  intro j hj hjD
  by_cases hj2 : j=2
  · subst j
    have hRemainder := scalar_binomial_quadratic_remainder_bound Q D M N B hD hN hB hHigher
    have he : ((2*M : ℕ) : ℝ)*Q.coeff 2 =
        (M : ℝ)*scalarPolynomialBinomialCoefficient Q D 2-
          (M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) := by push_cast; ring
    rw [he,AddCircle.coe_sub]
    have hnorm := norm_sub_le
      (((M : ℝ)*scalarPolynomialBinomialCoefficient Q D 2 : ℝ) : UnitAddCircle)
      (((M : ℝ)*(scalarPolynomialBinomialCoefficient Q D 2-2*Q.coeff 2) : ℝ) : UnitAddCircle)
    have hh := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (N : ℝ))
    nlinarith
  · have hhigh := hHigher j (by omega) hjD
    have he : ((2*M : ℕ) : ℝ)*Q.coeff j = (2 : ℝ)*((M : ℝ)*Q.coeff j) := by push_cast; ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (mod_one_natural_multiplier_norm_le 2 ((M : ℝ)*Q.coeff j))
      (pow_nonneg (Nat.cast_nonneg N) j)
    have hBudget : 0 ≤ (scalarBinomialCoefficientBudget D : ℝ) := Nat.cast_nonneg _
    have hExtra := mul_nonneg hBudget hB
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith

theorem scalar_quadratic_complete_tables (Q : ℝ[X]) (D M N : ℕ) (B : ℝ)
    (hD : 2 ≤ D) (hN : 0 < N) (hB : 0 ≤ B)
    (hSecond : (N : ℝ)^2*‖(((M : ℝ)*scalarPolynomialBinomialCoefficient Q D 2 : ℝ) : UnitAddCircle)‖ ≤ B)
    (hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ D → (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    let C := (1+(scalarBinomialCoefficientBudget D : ℝ))*(2+(scalarBinomialCoefficientBudget D : ℝ))*B
    (∀ j : ℕ, 2 ≤ j → j ≤ D → (N : ℝ)^j*‖((((2*M : ℕ) : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ C) ∧
    ∀ j : ℕ, 2 ≤ j → j ≤ D → (N : ℝ)^j*‖((((2*M : ℕ) : ℝ)*scalarPolynomialBinomialCoefficient Q D j : ℝ) : UnitAddCircle)‖ ≤ C := by
  have hMono := scalar_quadratic_complete_monomial_bound Q D M N B hD hN hB hSecond hHigher
  have hK : 0 ≤ (scalarBinomialCoefficientBudget D : ℝ) := Nat.cast_nonneg _
  have hBase : 0 ≤ (2+(scalarBinomialCoefficientBudget D : ℝ))*B := by positivity
  have hMonoC : (2+(scalarBinomialCoefficientBudget D : ℝ))*B ≤
      (1+(scalarBinomialCoefficientBudget D : ℝ))*(2+(scalarBinomialCoefficientBudget D : ℝ))*B := by nlinarith
  have hBinC : (scalarBinomialCoefficientBudget D : ℝ)*((2+(scalarBinomialCoefficientBudget D : ℝ))*B) ≤
      (1+(scalarBinomialCoefficientBudget D : ℝ))*(2+(scalarBinomialCoefficientBudget D : ℝ))*B := by nlinarith
  refine ⟨fun j hj hjD => (hMono j hj hjD).trans hMonoC,?_⟩
  intro j hj hjD
  exact (scalar_binomial_coefficient_mod_one Q D (2*M) j 2 hjD hj (N : ℝ) _
    (by exact_mod_cast hN) hBase hMono).trans hBinC

end Hindman168
