import Hindman168.AlignmentCubeModelParameters

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

variable {κ τ : Type*} [Fintype κ]

noncomputable def alignmentJointVertexPolynomial (weight : κ → ℤ) :
    MvPolynomial (Sum (Option κ) τ) ℝ :=
  X (Sum.inl none) + ∑ j, C (weight j : ℝ) * X (Sum.inl (some j))

noncomputable def alignmentJointTailPolynomial (T : Finset τ) :
    MvPolynomial (Sum (Option κ) τ) ℝ := ∏ j ∈ T, X (Sum.inr j)

noncomputable def alignmentJointBasePolynomial (M Y r rv s : ℝ)
    (weight : κ → ℤ) (T : Finset τ) : MvPolynomial (Sum (Option κ) τ) ℝ :=
  C (Y + (r - rv) / M) + alignmentJointVertexPolynomial weight +
    C (s / M) * alignmentJointTailPolynomial T

noncomputable def alignmentJointIncrementPolynomial (M q rho : ℝ) (T : Finset τ) :
    MvPolynomial (Sum (Option κ) τ) ℝ :=
  C (q / M) - C (rho / M) * alignmentJointTailPolynomial T

theorem alignmentJointVertexPolynomial_degree (weight : κ → ℤ) :
    (alignmentJointVertexPolynomial (τ := τ) weight).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X]; decide)

omit [Fintype κ] in
theorem alignmentJointTailPolynomial_degree (T : Finset τ) :
    (alignmentJointTailPolynomial (κ := κ) T).totalDegree ≤ T.card := by
  exact (totalDegree_finsetProd T _).trans (by simp)

theorem alignmentJointBasePolynomial_degree (M Y r rv s : ℝ)
    (weight : κ → ℤ) (T : Finset τ) :
    (alignmentJointBasePolynomial M Y r rv s weight T).totalDegree ≤ max 1 T.card := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le (by simp only [totalDegree_C]; omega)
    exact (alignmentJointVertexPolynomial_degree weight).trans (le_max_left _ _)
  · apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using
      (alignmentJointTailPolynomial_degree (κ := κ) T).trans (le_max_right 1 _)

omit [Fintype κ] in
theorem alignmentJointIncrementPolynomial_degree (M q rho : ℝ) (T : Finset τ) :
    (alignmentJointIncrementPolynomial (κ := κ) M q rho T).totalDegree ≤ T.card := by
  apply (totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add] using alignmentJointTailPolynomial_degree (κ := κ) T

theorem alignmentJointBasePolynomial_eval (M Y r rv s : ℝ)
    (weight : κ → ℤ) (T : Finset τ) (z : Option κ → ℝ) (t : τ → ℝ) :
    eval (Sum.elim z t) (alignmentJointBasePolynomial M Y r rv s weight T) =
      eval (fun b => if b then ∏ j ∈ T, t j else z none + ∑ j, weight j * z (some j))
        (alignmentCubeBasePolynomial M Y r rv s) := by
  simp only [alignmentJointBasePolynomial, alignmentJointVertexPolynomial,
    alignmentJointTailPolynomial, alignmentCubeBasePolynomial, map_add, map_mul,
    map_sum, map_prod, eval_C, eval_X, Sum.elim_inl, Sum.elim_inr,
    Bool.false_eq_true, ↓reduceIte]

omit [Fintype κ] in
theorem alignmentJointIncrementPolynomial_eval (M q rho : ℝ) (T : Finset τ)
    (z : Option κ → ℝ) (t : τ → ℝ) :
    eval (Sum.elim z t) (alignmentJointIncrementPolynomial M q rho T) =
      eval (fun b => if b then ∏ j ∈ T, t j else z none)
        (alignmentCubeIncrementPolynomial M q rho) := by
  simp only [alignmentJointIncrementPolynomial, alignmentJointTailPolynomial,
    alignmentCubeIncrementPolynomial, map_sub, map_mul, map_prod, eval_C, eval_X,
    Sum.elim_inr, ↓reduceIte]

end Hindman168
