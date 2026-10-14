import Hindman168.ScalarUnitPolynomial

/-! TRUE scalar-to-Unit polynomial conversion retains actual degree,
coefficients and real samples. No source filteredness is assumed. -/
namespace Hindman168
open Polynomial

noncomputable def scalarUnitMvPolynomial (P : ℝ[X]) : MvPolynomial Unit ℝ :=
  (MvPolynomial.uniqueAlgEquiv ℝ Unit).symm P

theorem scalar_unit_mv_polynomial_round_trip (P : ℝ[X]) :
    scalarUnitPolynomial (scalarUnitMvPolynomial P)=P :=
  (MvPolynomial.uniqueAlgEquiv ℝ Unit).apply_symm_apply P

theorem scalar_unit_mv_polynomial_eval (P : ℝ[X]) (x : Unit → ℝ) :
    MvPolynomial.eval x (scalarUnitMvPolynomial P)=P.eval (x ()) :=
  MvPolynomial.eval₂_uniqueAlgEquiv_symm

theorem scalar_unit_mv_polynomial_coeff (P : ℝ[X]) (J : Unit →₀ ℕ) :
    MvPolynomial.coeff J (scalarUnitMvPolynomial P)=P.coeff (J ()) :=
  MvPolynomial.coeff_uniqueAlgEquiv_symm ℝ P J

theorem scalar_unit_mv_polynomial_degree (P : ℝ[X]) (j : ℕ) (hj : P.natDegree ≤ j) :
    (scalarUnitMvPolynomial P).totalDegree ≤ j := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro J hJ
  have hne := MvPolynomial.mem_support_iff.mp hJ
  rw [scalar_unit_mv_polynomial_coeff] at hne
  have hSum : J.sum (fun _ n => n)=J () := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp
  rw [hSum]
  exact (Polynomial.le_natDegree_of_ne_zero hne).trans hj

end Hindman168
