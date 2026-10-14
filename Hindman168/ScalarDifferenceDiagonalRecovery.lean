import Hindman168.ScalarTaylorTailNorm
import Hindman168.ModOneNaturalMultiplier
import Hindman168.ScalarBinomialCoefficientModOne

/-! Actual higher diagonal coefficients are recovered by subtracting the
PROVED small nonlinear Taylor tail, never by separating small summands. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_difference_diagonal_coefficient_bound (P Q : ℝ[X]) (D M i h N : ℕ)
    (A B : ℝ) (hQ : Q.natDegree ≤ D) (hi2 : 2 ≤ i) (hiD : i ≤ D)
    (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B) (σ : ℝ)
    (hR : (N : ℝ)^i*‖((scalarDifferencePolynomial P Q h σ).coeff i : UnitAddCircle)‖ ≤ A)
    (hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)^i*‖(((M : ℝ)*P.coeff i : ℝ) : UnitAddCircle)‖ ≤
      (M : ℝ)*A+(scalarTaylorTailBudget D : ℝ)*B := by
  have he : (M : ℝ)*P.coeff i = (M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff i-
      (M : ℝ)*scalarTaylorTail Q D i h := by
    rw [scalar_difference_coefficient_tail P Q D i h σ hQ hiD hi2]
    ring
  have hScaled : (N : ℝ)^i*‖(((M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff i : ℝ) :
      UnitAddCircle)‖ ≤ (M : ℝ)*A := by
    have hm := mod_one_natural_multiplier_norm_le M ((scalarDifferencePolynomial P Q h σ).coeff i)
    calc
      _ ≤ (N : ℝ)^i*((M : ℝ)*‖((scalarDifferencePolynomial P Q h σ).coeff i : UnitAddCircle)‖) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (M : ℝ)*((N : ℝ)^i*‖((scalarDifferencePolynomial P Q h σ).coeff i : UnitAddCircle)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg M)
  rw [he,AddCircle.coe_sub]
  have hTriangle := mul_le_mul_of_nonneg_left
    (norm_sub_le (((M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff i : ℝ) : UnitAddCircle)
      (((M : ℝ)*scalarTaylorTail Q D i h : ℝ) : UnitAddCircle)) (by positivity : 0 ≤ (N : ℝ)^i)
  rw [mul_add] at hTriangle
  exact hTriangle.trans (add_le_add hScaled
    (scalar_taylor_tail_norm Q D M i h N B hiD hi2 hN hh hB hHigher))

theorem scalar_difference_linear_residual_bound (P Q : ℝ[X]) (D M h N : ℕ)
    (A B : ℝ) (hQ : Q.natDegree ≤ D) (hD : 2 ≤ D)
    (hN : 0 < N) (hh : h ≤ N) (hB : 0 ≤ B) (σ : ℝ)
    (hR : (N : ℝ)*‖((scalarDifferencePolynomial P Q h σ).coeff 1 : UnitAddCircle)‖ ≤ A)
    (hHigher : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    (N : ℝ)*‖(((M : ℝ)*(P.coeff 1+2*Q.coeff 2*(h : ℝ)+σ) : ℝ) : UnitAddCircle)‖ ≤
      (M : ℝ)*A+(scalarTaylorTailBudget D : ℝ)*B := by
  have he : (M : ℝ)*(P.coeff 1+2*Q.coeff 2*(h : ℝ)+σ) =
      (M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff 1-
      (M : ℝ)*scalarTaylorHighLinearTail Q D h := by
    rw [scalar_difference_linear_high_tail P Q D h σ hQ hD]
    ring
  have hScaled : (N : ℝ)*‖(((M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff 1 : ℝ) :
      UnitAddCircle)‖ ≤ (M : ℝ)*A := by
    have hm := mod_one_natural_multiplier_norm_le M ((scalarDifferencePolynomial P Q h σ).coeff 1)
    calc
      _ ≤ (N : ℝ)*((M : ℝ)*‖((scalarDifferencePolynomial P Q h σ).coeff 1 : UnitAddCircle)‖) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg N)
      _ = (M : ℝ)*((N : ℝ)*‖((scalarDifferencePolynomial P Q h σ).coeff 1 : UnitAddCircle)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg M)
  rw [he,AddCircle.coe_sub]
  have hTriangle := mul_le_mul_of_nonneg_left
    (norm_sub_le (((M : ℝ)*(scalarDifferencePolynomial P Q h σ).coeff 1 : ℝ) : UnitAddCircle)
      (((M : ℝ)*scalarTaylorHighLinearTail Q D h : ℝ) : UnitAddCircle)) (Nat.cast_nonneg (α := ℝ) N)
  rw [mul_add] at hTriangle
  exact hTriangle.trans (add_le_add hScaled
    (scalar_taylor_high_linear_tail_norm Q D M h N B (by omega) hN hh hB hHigher))

end Hindman168
