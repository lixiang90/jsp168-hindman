import Hindman168.ScalarVariableEquiv
import Hindman168.MvBinomialCoefficients

/-! COMPLETE actual paper-binomial coefficients commute with genuine
finite variable equivalence, retaining original multi-index weights. -/

namespace Hindman168
open scoped BigOperators
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem mv_binomial_variable_equiv_box (e : σ ≃ τ) (d : ℕ) (J : σ → ℕ) :
    J ∈ mvBinomialBox σ d ↔ scalarVariableAssignmentEquiv e ℕ J ∈ mvBinomialBox τ d := by
  rw [mv_binomial_box_mem,mv_binomial_box_mem]
  constructor
  · exact fun h j => h (e.symm j)
  · intro h i
    simpa only [scalar_variable_equiv_apply,Equiv.symm_apply_apply] using h (e i)

theorem mv_binomial_variable_equiv_stirling (e : σ ≃ τ) (I J : σ → ℕ) :
    mvBinomialStirlingWeight (scalarVariableAssignmentEquiv e ℕ I) (scalarVariableAssignmentEquiv e ℕ J) =
      mvBinomialStirlingWeight I J := by
  unfold mvBinomialStirlingWeight
  symm
  exact Fintype.prod_equiv e (fun i => (I i).factorial * Nat.stirlingSecond (J i) (I i))
    (fun j => (scalarVariableAssignmentEquiv e ℕ I j).factorial *
      Nat.stirlingSecond (scalarVariableAssignmentEquiv e ℕ J j) (scalarVariableAssignmentEquiv e ℕ I j))
    (fun i => by simp only [scalar_variable_equiv_apply,Equiv.symm_apply_apply])

theorem mv_binomial_variable_equiv_coefficient (e : σ ≃ τ) (p : MvPolynomial σ ℝ) (d : ℕ) (I : σ → ℕ) :
    mvPolynomialBinomialCoefficient (MvPolynomial.rename e p) d (scalarVariableAssignmentEquiv e ℕ I) =
      mvPolynomialBinomialCoefficient p d I := by
  classical
  unfold mvPolynomialBinomialCoefficient
  symm
  apply Finset.sum_equiv (scalarVariableAssignmentEquiv e ℕ)
  · exact mv_binomial_variable_equiv_box e d
  · intro J _
    rw [scalar_variable_equiv_coefficient,mv_binomial_variable_equiv_stirling]

end Hindman168
