import Hindman168.RoughBinomialDenominator

namespace Hindman168
open MvPolynomial
open scoped BigOperators

noncomputable def adaptedTaylorBinomial (j : ℕ) : MvPolynomial Unit ℝ :=
  C ((j.factorial : ℝ)⁻¹) * ∏ m ∈ Finset.range j, (X () - C (m : ℝ))

theorem adapted_taylor_binomial_degree (j : ℕ) :
    (adaptedTaylorBinomial j).totalDegree ≤ j := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _m ∈ Finset.range j, 1 := by
      apply Finset.sum_le_sum
      intro m _
      exact (totalDegree_sub_C_le _ _).trans_eq (totalDegree_X ())
    _ = j := by simp

theorem adapted_taylor_binomial_eval_nat (j m : ℕ) :
    eval (fun _ : Unit => (m : ℝ)) (adaptedTaylorBinomial j) = (m.choose j : ℝ) := by
  have h := rough_mv_binomial_eval_nat (fun _ : Unit => j) (fun _ => m)
  simpa only [roughMvBinomialPolynomial, roughMvFallingPolynomial,
    Finset.univ_unique, Finset.prod_singleton, adaptedTaylorBinomial] using h

end Hindman168
