import Hindman168.PolynomialSmallValuesInverse
import Mathlib.Algebra.Polynomial.Taylor

/-! Exact second coefficient of P+Q(X+h)-Q+sigma*X.
The arbitrary sigma term vanishes from this actual coefficient. -/
namespace Hindman168
open Polynomial

noncomputable def scalarDifferencePolynomial (P Q : ℝ[X]) (h σ : ℝ) : ℝ[X] :=
  P+Q.comp (X+C h)-Q+C σ*X

noncomputable def scalarDifferenceSecondFamily (P Q : ℝ[X]) : ℝ[X] :=
  hasseDeriv 2 Q+C (P.coeff 2-Q.coeff 2)

theorem scalar_difference_second_family_eval (P Q : ℝ[X]) (h σ : ℝ) :
    (scalarDifferenceSecondFamily P Q).eval h = (scalarDifferencePolynomial P Q h σ).coeff 2 := by
  rw [scalarDifferenceSecondFamily,eval_add,eval_C,scalarDifferencePolynomial,
    coeff_add,coeff_sub,coeff_add]
  have ht : (Q.comp (X+C h)).coeff 2 = (hasseDeriv 2 Q).eval h :=
    taylor_coeff h Q 2
  rw [ht,coeff_C_mul,coeff_X]
  norm_num
  ring

theorem scalar_difference_second_family_degree (P Q : ℝ[X]) (D : ℕ) (hQ : Q.natDegree ≤ D) :
    (scalarDifferenceSecondFamily P Q).natDegree ≤ D := by
  apply (natDegree_add_le _ _).trans
  exact max_le ((natDegree_hasseDeriv_le Q 2).trans ((Nat.sub_le _ _).trans hQ))
    (by simpa only [natDegree_C] using Nat.zero_le D)

theorem scalar_difference_second_family_coefficient (P Q : ℝ[X]) (j : ℕ) (hj : 0 < j) :
    (scalarDifferenceSecondFamily P Q).coeff j = ((j+2).choose 2 : ℝ)*Q.coeff (j+2) := by
  rw [scalarDifferenceSecondFamily,coeff_add,hasseDeriv_coeff,coeff_C]
  simp only [if_neg (Nat.ne_of_gt hj),add_zero]

end Hindman168
