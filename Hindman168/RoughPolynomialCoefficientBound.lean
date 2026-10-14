import Hindman168.RoughInterpolationNodes

namespace Hindman168
open Polynomial
open scoped BigOperators

noncomputable def roughPolynomialCoeffMass (P : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j|

theorem roughPolynomialCoeffMass_nonneg (P : ℝ[X]) : 0 ≤ roughPolynomialCoeffMass P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem rough_polynomial_eval_bound (P : ℝ[X]) (q : ℕ) (hP : P.natDegree ≤ q)
    (B x : ℝ) (hB : 1 ≤ B) (hx : |x| ≤ B) :
    |P.eval x| ≤ roughPolynomialCoeffMass P * B ^ q := by
  rw [eval_eq_sum_range, roughPolynomialCoeffMass, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul, abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hjq : j ≤ q := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hP
  exact (pow_le_pow_left₀ (abs_nonneg _) hx j).trans (pow_le_pow_right₀ hB hjq)

end Hindman168
