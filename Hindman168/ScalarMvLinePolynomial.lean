import Hindman168.RoughMvAffineSubstitution
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

namespace Hindman168
open scoped BigOperators Classical

/-- The actual substitution x_j + u_j*t, with t the extra `none` variable. -/
noncomputable def scalarMvLineLift {κ : Type*} (p : MvPolynomial κ ℝ) (u : κ → ℝ) :
    MvPolynomial (Option κ) ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C (fun j =>
    MvPolynomial.X (some j)+MvPolynomial.C (u j)*MvPolynomial.X none) p

noncomputable def scalarMvLineCoefficient {κ : Type*}
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) (r : ℕ) : MvPolynomial κ ℝ :=
  ((MvPolynomial.optionEquivLeft ℝ κ) (scalarMvLineLift p u)).coeff r

noncomputable def scalarMvLinePolynomial {κ : Type*}
    (p : MvPolynomial κ ℝ) (x u : κ → ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval x)
    ((MvPolynomial.optionEquivLeft ℝ κ) (scalarMvLineLift p u))

theorem scalar_mv_line_lift_degree {κ : Type*} (p : MvPolynomial κ ℝ) (u : κ → ℝ) :
    (scalarMvLineLift p u).totalDegree ≤ p.totalDegree := by
  apply rough_mv_linear_substitution_degree
  intro j
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem scalar_mv_line_lift_eval {κ : Type*}
    (p : MvPolynomial κ ℝ) (x u : κ → ℝ) (t : ℝ) :
    MvPolynomial.eval (fun j => Option.elim j t x) (scalarMvLineLift p u) =
      MvPolynomial.eval (fun j => x j+u j*t) p := by
  dsimp only [scalarMvLineLift]
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun v : κ → ℝ => MvPolynomial.eval v p)
  funext j
  simp only [Function.comp_apply, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Option.elim_some, Option.elim_none]

theorem scalar_mv_line_polynomial_eval {κ : Type*}
    (p : MvPolynomial κ ℝ) (x u : κ → ℝ) (t : ℝ) :
    (scalarMvLinePolynomial p x u).eval t = MvPolynomial.eval (fun j => x j+u j*t) p := by
  rw [scalarMvLinePolynomial, ← MvPolynomial.optionEquivLeft_elim_eval,
    scalar_mv_line_lift_eval]

theorem scalar_mv_line_polynomial_coefficient {κ : Type*}
    (p : MvPolynomial κ ℝ) (x u : κ → ℝ) (r : ℕ) :
    (scalarMvLinePolynomial p x u).coeff r =
      MvPolynomial.eval x (scalarMvLineCoefficient p u r) := by
  rw [scalarMvLinePolynomial, Polynomial.coeff_map]
  rfl

theorem scalar_mv_line_polynomial_degree {κ : Type*}
    (p : MvPolynomial κ ℝ) (u x : κ → ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    (scalarMvLinePolynomial p x u).natDegree ≤ D := by
  apply Polynomial.natDegree_map_le.trans
  rw [MvPolynomial.natDegree_optionEquivLeft]
  exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
    ((scalar_mv_line_lift_degree p u).trans hp)

/-- Every positive line coefficient is a genuinely lower-degree polynomial
in the ORIGINAL basepoint. This is derived from the actual lifted polynomial. -/
theorem scalar_mv_line_coefficient_degree {κ : Type*}
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) (D r : ℕ) (hp : p.totalDegree ≤ D) :
    (scalarMvLineCoefficient p u r).totalDegree ≤ D-r := by
  have htotal := (scalar_mv_line_lift_degree p u).trans hp
  by_cases hr : r ≤ (scalarMvLineLift p u).totalDegree
  · have h := MvPolynomial.totalDegree_coeff_optionEquivLeft_add_le ℝ κ (scalarMvLineLift p u) r hr
    change (scalarMvLineCoefficient p u r).totalDegree+r ≤ (scalarMvLineLift p u).totalDegree at h
    omega
  · have hz : ((MvPolynomial.optionEquivLeft ℝ κ) (scalarMvLineLift p u)).coeff r = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [MvPolynomial.natDegree_optionEquivLeft]
      exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans_lt (Nat.lt_of_not_ge hr)
    rw [scalarMvLineCoefficient, hz]
    simp

theorem scalar_mv_line_coefficient_scale {κ : Type*}
    (p : MvPolynomial κ ℝ) (u : κ → ℝ) (r : ℕ) (a : ℝ) :
    scalarMvLineCoefficient (MvPolynomial.C a*p) u r =
      MvPolynomial.C a*scalarMvLineCoefficient p u r := by
  simp only [scalarMvLineCoefficient, scalarMvLineLift, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, map_mul, MvPolynomial.optionEquivLeft_C, Polynomial.coeff_C_mul]

end Hindman168
