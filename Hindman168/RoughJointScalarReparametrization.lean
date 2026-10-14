import Hindman168.RoughJointCoefficientPolynomial
import Hindman168.RoughAffinePolynomial

namespace Hindman168
open MvPolynomial

theorem rough_joint_scalar_reparametrization {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (P0 : Polynomial R) (theta : (κ →₀ ℕ) → Polynomial R)
    (a b z : R) (y : κ → R) :
    eval (Option.elim · z y) (roughSpatialJointPolynomial s
      (P0.comp (Polynomial.C a+Polynomial.C b*Polynomial.X))
      (fun J => (theta J).comp (Polynomial.C a+Polynomial.C b*Polynomial.X))) =
    eval (Option.elim · (a+b*z) y) (roughSpatialJointPolynomial s P0 theta) := by
  rw [roughSpatialJointPolynomial_eval, roughSpatialJointPolynomial_eval]
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem rough_joint_scalar_reparametrized_degree {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (P0 : Polynomial R) (theta : (κ →₀ ℕ) → Polynomial R)
    (q : ℕ) (h0 : P0.natDegree ≤ q)
    (hθ : ∀ J ∈ s, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) (a b : R) :
    (P0.comp (Polynomial.C a+Polynomial.C b*Polynomial.X)).natDegree ≤ q ∧
    (∀ J ∈ s, ((theta J).comp (Polynomial.C a+Polynomial.C b*Polynomial.X)).natDegree+
      J.sum (fun _ e => e) ≤ q) ∧
    (roughSpatialJointPolynomial s (P0.comp (Polynomial.C a+Polynomial.C b*Polynomial.X))
      (fun J => (theta J).comp (Polynomial.C a+Polynomial.C b*Polynomial.X))).totalDegree ≤ q := by
  have h0' := (rough_affine_comp_degree P0 a b).trans h0
  have hθ' : ∀ J ∈ s, ((theta J).comp (Polynomial.C a+Polynomial.C b*Polynomial.X)).natDegree+
      J.sum (fun _ e => e) ≤ q := by
    intro J hJ
    exact (Nat.add_le_add_right (rough_affine_comp_degree (theta J) a b) _).trans (hθ J hJ)
  exact ⟨h0', hθ', roughSpatialJointPolynomial_degree _ _ _ _ h0' hθ'⟩

theorem rough_linear_step_weighted_degree {R : Type*} [Semiring R]
    (theta : Polynomial R) (a b : R) (e q : ℕ) (h : theta.natDegree+e ≤ q) :
    ((Polynomial.C a+Polynomial.C b*Polynomial.X)^e*theta).natDegree ≤ q := by
  have hlin : (Polynomial.C a+Polynomial.C b*Polynomial.X : Polynomial R).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hpow : ((Polynomial.C a+Polynomial.C b*Polynomial.X : Polynomial R)^e).natDegree ≤ e := by
    exact Polynomial.natDegree_pow_le.trans (by simpa only [mul_one] using Nat.mul_le_mul_left e hlin)
  exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add_right hpow theta.natDegree).trans
    (by simpa only [Nat.add_comm] using h))

end Hindman168
