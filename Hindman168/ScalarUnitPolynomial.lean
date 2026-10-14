import Hindman168.MvScalarTranslation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! Exact Unit-variable/univariate scalar polynomial conversion, including
ALL coefficients, actual evaluations, degree and original translations. -/
namespace Hindman168
open Polynomial

noncomputable def scalarUnitPolynomial (p : MvPolynomial Unit ℝ) : ℝ[X] :=
  MvPolynomial.uniqueAlgEquiv ℝ Unit p

theorem scalar_unit_polynomial_coefficient (p : MvPolynomial Unit ℝ) (j : ℕ) :
    (scalarUnitPolynomial p).coeff j = MvPolynomial.coeff (Finsupp.single () j) p :=
  MvPolynomial.coeff_uniqueAlgEquiv ℝ p j

theorem scalar_unit_polynomial_eval (p : MvPolynomial Unit ℝ) (x : ℝ) :
    (scalarUnitPolynomial p).eval x = MvPolynomial.eval (fun _ => x) p :=
  MvPolynomial.eval₂_const_uniqueAlgEquiv

theorem scalar_unit_polynomial_degree (p : MvPolynomial Unit ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    (scalarUnitPolynomial p).natDegree ≤ D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [scalar_unit_polynomial_coefficient]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  have hj0 : j ≠ 0 := by omega
  simpa [Finsupp.support_single () hj0] using hp.trans_lt hj

theorem scalar_unit_polynomial_translation (p : MvPolynomial Unit ℝ) (h : ℝ) :
    scalarUnitPolynomial (mvScalarTranslation p (fun _ => h)) =
      (scalarUnitPolynomial p).comp (Polynomial.X+Polynomial.C h) := by
  apply Polynomial.funext
  intro x
  rw [scalar_unit_polynomial_eval,mv_scalar_translation_eval,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,scalar_unit_polynomial_eval]

theorem scalar_unit_polynomial_C (x : ℝ) : scalarUnitPolynomial (MvPolynomial.C x) = Polynomial.C x :=
  (MvPolynomial.uniqueAlgEquiv ℝ Unit).commutes x

theorem scalar_unit_polynomial_X : scalarUnitPolynomial (MvPolynomial.X ()) = Polynomial.X := by
  apply Polynomial.funext
  intro x
  rw [scalar_unit_polynomial_eval,MvPolynomial.eval_X,Polynomial.eval_X]

end Hindman168
