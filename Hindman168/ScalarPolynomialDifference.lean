import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

namespace Hindman168
open Polynomial

noncomputable def scalarPolynomialDifference (p : ℝ[X]) (h : ℝ) : ℝ[X] := p.taylor h-p

theorem scalar_polynomial_difference_eval (p : ℝ[X]) (h x : ℝ) :
    (scalarPolynomialDifference p h).eval x = p.eval (x+h)-p.eval x := by
  simp only [scalarPolynomialDifference, eval_sub, taylor_apply, eval_comp,
    eval_add, eval_X, eval_C]

/-- The actual translated polynomial difference has degree at most one less
than a fixed positive degree bound, including a vanishing difference. -/
theorem scalar_polynomial_difference_degree_le (p : ℝ[X]) (h : ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d+1) : (scalarPolynomialDifference p h).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [scalarPolynomialDifference, coeff_sub]
  by_cases htop : k=p.natDegree
  · rw [htop, coeff_taylor_natDegree, coeff_natDegree, sub_self]
  · have hkp : p.natDegree < k := by omega
    rw [coeff_eq_zero_of_natDegree_lt hkp,
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hkp), sub_self]

/-- The actual coefficient immediately below the degree bound is d*h*alpha_d.
This holds even if the actual degree is strictly below the bound. -/
theorem scalar_polynomial_difference_top_coefficient (p : ℝ[X]) (h : ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d+1) :
    (scalarPolynomialDifference p h).coeff d = (d+1 : ℕ)*h*p.coeff (d+1) := by
  have hdeg : (p.hasseDeriv d).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le p d).trans (by omega)
  rw [scalarPolynomialDifference, coeff_sub, taylor_coeff,
    eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul, Nat.add_comm 1 d, Nat.choose_succ_self_right]
  ring

end Hindman168
