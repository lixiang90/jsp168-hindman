import Hindman168.ScalarPolynomialPhaseLags

namespace Hindman168
open Polynomial

noncomputable def scalarPolynomialDropTop (p : ℝ[X]) (d : ℕ) : ℝ[X] := p-monomial d (p.coeff d)

theorem scalar_polynomial_drop_top_degree (p : ℝ[X]) (d : ℕ) (hp : p.natDegree ≤ d+1) :
    (scalarPolynomialDropTop p (d+1)).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [scalarPolynomialDropTop, coeff_sub, coeff_monomial]
  by_cases he : d+1=k
  · rw [if_pos he, ← he, sub_self]
  · rw [if_neg he, sub_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem scalar_polynomial_drop_top_eval (p : ℝ[X]) (d : ℕ) (x : ℝ) :
    (scalarPolynomialDropTop p d).eval x = p.eval x-p.coeff d*x^d := by
  simp only [scalarPolynomialDropTop, eval_sub, eval_monomial]

theorem scalar_polynomial_top_phase_factor (p : ℝ[X]) (d n : ℕ) :
    scalarPolynomialPhase p n =
      (AddCircle.toCircle (((p.coeff d*(n : ℝ)^d : ℝ)) : UnitAddCircle) : ℂ)*
        scalarPolynomialPhase (scalarPolynomialDropTop p d) n := by
  have he : p.eval (n : ℝ) = p.coeff d*(n : ℝ)^d+(scalarPolynomialDropTop p d).eval (n : ℝ) := by
    rw [scalar_polynomial_drop_top_eval]
    ring
  rw [scalarPolynomialPhase, he, AddCircle.coe_add, AddCircle.toCircle_add, Circle.coe_mul]
  rfl

theorem scalar_polynomial_top_phase_error (p : ℝ[X]) (d n a : ℕ) :
    ‖scalarPolynomialPhase p n-
      (AddCircle.toCircle (((p.coeff d*(a : ℝ)^d : ℝ)) : UnitAddCircle) : ℂ)*
        scalarPolynomialPhase (scalarPolynomialDropTop p d) n‖ =
      ‖(AddCircle.toCircle (((p.coeff d*(n : ℝ)^d : ℝ)) : UnitAddCircle) : ℂ)-
        (AddCircle.toCircle (((p.coeff d*(a : ℝ)^d : ℝ)) : UnitAddCircle) : ℂ)‖ := by
  rw [scalar_polynomial_top_phase_factor, ← sub_mul, norm_mul,
    scalar_polynomial_phase_norm, mul_one]

noncomputable def scalarPolynomialOnProgression (p : ℝ[X]) (a q : ℕ) : ℝ[X] :=
  p.comp (C (q : ℝ)*X+C (a : ℝ))

theorem scalar_polynomial_on_progression_eval (p : ℝ[X]) (a q : ℕ) (x : ℝ) :
    (scalarPolynomialOnProgression p a q).eval x = p.eval ((a : ℝ)+(q : ℝ)*x) := by
  simp only [scalarPolynomialOnProgression, eval_comp, eval_add, eval_mul, eval_C, eval_X]
  rw [add_comm]

theorem scalar_polynomial_on_progression_degree (p : ℝ[X]) (a q d : ℕ) (hp : p.natDegree ≤ d) :
    (scalarPolynomialOnProgression p a q).natDegree ≤ d := by
  apply natDegree_comp_le.trans
  have hh : (C (q : ℝ)*X+C (a : ℝ)).natDegree ≤ 1 := by compute_degree
  exact (Nat.mul_le_mul_left p.natDegree hh).trans (by simpa only [mul_one] using hp)

theorem scalar_polynomial_on_progression_phase (p : ℝ[X]) (a q n : ℕ) :
    scalarPolynomialPhase (scalarPolynomialOnProgression p a q) n = scalarPolynomialPhase p (a+q*n) := by
  simp only [scalarPolynomialPhase, scalar_polynomial_on_progression_eval, Nat.cast_add, Nat.cast_mul]

end Hindman168
