import Hindman168.ScalarPolynomialTopRemoval
import Mathlib.Algebra.Polynomial.Coeff

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_polynomial_taylor_coefficient_sum (p : ℝ[X]) (a : ℝ) (D i : ℕ)
    (hp : p.natDegree ≤ D) :
    (p.taylor a).coeff i = ∑ j ∈ Finset.range (D+1),
      p.coeff j*(j.choose i : ℝ)*a^(j-i) := by
  conv_lhs => rw [p.as_sum_range' (D+1) (by omega)]
  simp only [map_sum, finsetSum_coeff, taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem scalar_polynomial_progression_coefficient (p : ℝ[X]) (a q i : ℕ) :
    (scalarPolynomialOnProgression p a q).coeff i = (p.taylor (a : ℝ)).coeff i*(q : ℝ)^i := by
  have he : scalarPolynomialOnProgression p a q = (p.taylor (a : ℝ)).comp (C (q : ℝ)*X) := by
    rw [scalarPolynomialOnProgression, taylor_apply, comp_assoc]
    simp only [add_comp, X_comp, C_comp]
  rw [he, comp_C_mul_X_coeff]

def scalarProgressionRecoveryWeight (a q D i j : ℕ) : ℤ :=
  (q : ℤ)^(D-j)*(j.choose i : ℤ)*(-(a : ℤ))^(j-i)

/-- True recovery of original coefficients from the actual affine
substitution, after clearing the scale by an integer power. Every recovery
weight is an actual integer; no quotient-circle division is asserted. -/
theorem scalar_polynomial_integer_coefficient_recovery (p : ℝ[X]) (a q D i : ℕ)
    (hp : p.natDegree ≤ D) :
    (q : ℝ)^D*p.coeff i = ∑ j ∈ Finset.range (D+1),
      (scalarProgressionRecoveryWeight a q D i j : ℝ)*(scalarPolynomialOnProgression p a q).coeff j := by
  have hInv : (p.taylor (a : ℝ)).taylor (-(a : ℝ)) = p := by
    rw [taylor_taylor, neg_add_cancel, taylor_zero]
  have hsum := scalar_polynomial_taylor_coefficient_sum (p.taylor (a : ℝ)) (-(a : ℝ)) D i
    (by simpa only [natDegree_taylor] using hp)
  rw [hInv] at hsum
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjD : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : (q : ℝ)^(D-j)*(q : ℝ)^j = (q : ℝ)^D := by
    rw [← pow_add, Nat.sub_add_cancel hjD]
  rw [scalar_polynomial_progression_coefficient]
  simp only [scalarProgressionRecoveryWeight, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_natCast]
  rw [← hpow]
  ring

theorem scalar_progression_recovery_weight_zero_below (a q D i j : ℕ) (hji : j < i) :
    scalarProgressionRecoveryWeight a q D i j = 0 := by
  simp only [scalarProgressionRecoveryWeight, Nat.choose_eq_zero_of_lt hji,
    Nat.cast_zero, mul_zero, zero_mul]

end Hindman168
