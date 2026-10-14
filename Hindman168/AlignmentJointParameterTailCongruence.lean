import Hindman168.AlignmentExposedJointParameters

/-! Original exposed exponent polynomials read only the actual tail set.
Other frozen values cannot enlarge the removed-factor exceptional event. -/
namespace Hindman168
open scoped BigOperators

theorem alignment_joint_base_tail_eval_congr {κ τ : Type*} [Fintype κ]
    (M Y r rv s : ℝ) (weight : κ → ℤ) (T : Finset τ) (z : Option κ → ℝ)
    (a b : τ → ℝ) (h : ∀ j ∈ T, a j=b j) :
    MvPolynomial.eval (Sum.elim z a) (alignmentJointBasePolynomial M Y r rv s weight T)=
      MvPolynomial.eval (Sum.elim z b) (alignmentJointBasePolynomial M Y r rv s weight T) := by
  rw [alignmentJointBasePolynomial_eval,alignmentJointBasePolynomial_eval]
  have hp : (∏ j ∈ T, a j)=(∏ j ∈ T, b j) := Finset.prod_congr rfl h
  rw [hp]

theorem alignment_joint_increment_tail_eval_congr {κ τ : Type*}
    (M q rho : ℝ) (T : Finset τ) (z : Option κ → ℝ)
    (a b : τ → ℝ) (h : ∀ j ∈ T, a j=b j) :
    MvPolynomial.eval (Sum.elim z a) (alignmentJointIncrementPolynomial M q rho T)=
      MvPolynomial.eval (Sum.elim z b) (alignmentJointIncrementPolynomial M q rho T) := by
  rw [alignmentJointIncrementPolynomial_eval,alignmentJointIncrementPolynomial_eval]
  have hp : (∏ j ∈ T, a j)=(∏ j ∈ T, b j) := Finset.prod_congr rfl h
  rw [hp]

theorem alignment_exposed_joint_base_tail_eval_congr {κ : Type*} [Fintype κ] {N : ℕ}
    (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N))
    (x : Fin N → ℕ) (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ)
    (z : Option κ → ℝ) (a b : Fin N → ℝ) (h : ∀ j ∈ T, a j=b j) :
    MvPolynomial.eval (Sum.elim z a) (alignmentExposedJointBasePolynomial F q₀ w i T x shift weight)=
      MvPolynomial.eval (Sum.elim z b) (alignmentExposedJointBasePolynomial F q₀ w i T x shift weight) := by
  unfold alignmentExposedJointBasePolynomial
  exact alignment_joint_base_tail_eval_congr _ _ _ _ _ weight T z a b h

theorem alignment_exposed_joint_increment_tail_eval_congr {κ : Type*} {N : ℕ}
    (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N))
    (x : Fin N → ℕ) (e : AlignmentAddingPair N i)
    (z : Option κ → ℝ) (a b : Fin N → ℝ) (h : ∀ j ∈ T, a j=b j) :
    MvPolynomial.eval (Sum.elim z a) (alignmentExposedJointIncrementPolynomial F q₀ w i T x e)=
      MvPolynomial.eval (Sum.elim z b) (alignmentExposedJointIncrementPolynomial F q₀ w i T x e) := by
  unfold alignmentExposedJointIncrementPolynomial
  exact alignment_joint_increment_tail_eval_congr _ _ _ T z a b h

end Hindman168
