import Hindman168.ScalarMvLinePolynomial
import Mathlib.Algebra.Polynomial.Roots

namespace Hindman168
open scoped BigOperators Classical

/-- The actual restriction at zero basepoint, grouped by ORIGINAL total degree. -/
theorem scalar_mv_line_zero_expansion {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) :
    scalarMvLinePolynomial p (fun _ => 0) u =
      ∑ I ∈ p.support,
        Polynomial.C (MvPolynomial.coeff I p*∏ j, u j^(I j))*
          Polynomial.X^(∑ j, I j) := by
  apply Polynomial.funext
  intro t
  rw [scalar_mv_line_polynomial_eval]
  simp only [zero_add]
  calc
    _ = MvPolynomial.eval (fun j => u j*t)
        (∑ I ∈ p.support, MvPolynomial.monomial I (MvPolynomial.coeff I p)) :=
      congrArg (MvPolynomial.eval (fun j => u j*t)) p.as_sum
    _ = _ := by
      simp only [map_sum, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      apply Finset.sum_congr rfl
      intro I _
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring

/-- The constant of the r-th line-coefficient polynomial is the ACTUAL
homogeneous degree-r direction evaluation of the ORIGINAL polynomial. -/
theorem scalar_mv_line_coefficient_constant {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) (r : ℕ) :
    MvPolynomial.coeff 0 (scalarMvLineCoefficient p u r) =
      ∑ I ∈ p.support.filter (fun I => (∑ j, I j)=r),
        MvPolynomial.coeff I p*∏ j, u j^(I j) := by
  have h := scalar_mv_line_polynomial_coefficient p (fun _ => 0) u r
  rw [scalar_mv_line_zero_expansion, Polynomial.finsetSum_coeff,
    MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at h
  rw [Finset.sum_filter]
  simpa only [Polynomial.coeff_C_mul_X_pow, eq_comm] using h.symm

end Hindman168
