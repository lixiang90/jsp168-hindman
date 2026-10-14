import Hindman168.AlignmentNativeArrayLogPolynomial
import Hindman168.AlignmentNativeModelArrays

namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ θ : Type*} [Fintype σ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

noncomputable def alignmentSelectedExponentPolynomial
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) (j : Fin (n + 1)) : MvPolynomial θ ℝ :=
  P + ∑ e, MvPolynomial.C (u j e : ℝ) * Q e

theorem alignmentSelectedExponentPolynomial_degree
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) (d : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : ∀ e, (Q e).totalDegree ≤ d) (j : Fin (n + 1)) :
    (alignmentSelectedExponentPolynomial n u P Q j).totalDegree ≤ d := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le hP
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, zero_add] using hQ e

noncomputable def alignmentNativeModelLogPolynomial (g b : G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) : MvPolynomial θ ℝ :=
  alignmentNativeArrayLogPolynomial n u (fun _ => g) (fun _ => b) ell
    (alignmentSelectedExponentPolynomial n u P Q)

theorem alignmentNativeModelLogPolynomial_degree (g b : G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) (s d : ℕ)
    (hs : Group.nilpotencyClass G ≤ s) (hP : P.totalDegree ≤ d) (hQ : ∀ e, (Q e).totalDegree ≤ d) :
    (alignmentNativeModelLogPolynomial n u g b ell P Q).totalDegree ≤ ((s * s + 1) ^ (s + 1)) * d :=
  alignmentNativeArrayLogPolynomial_degree n u _ _ _ _ s d hs
    (alignmentSelectedExponentPolynomial_degree n u P Q d hP hQ)

theorem alignmentNativeModelLogPolynomial_eval (g b : G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : MvPolynomial θ ℝ) (Q : σ → MvPolynomial θ ℝ) (z : θ → ℝ)
    (k : ℤ) (delta : σ → ℤ) (hP : MvPolynomial.eval z P = (k : ℝ))
    (hQ : ∀ e, MvPolynomial.eval z (Q e) = (delta e : ℝ)) :
    MvPolynomial.eval z (alignmentNativeModelLogPolynomial n u g b ell P Q) =
      ell (alignmentNativeCoefficientLog n u hu (alignmentNativeModelArray n u hu g b k delta)) := by
  apply alignmentNativeArrayLogPolynomial_eval n u hu _ _ _ _ z
    (fun j => k + ∑ e, u j e * delta e)
  · intro j
    simp only [alignmentSelectedExponentPolynomial, map_add, map_sum, map_mul,
      MvPolynomial.eval_C, hP, hQ, Int.cast_add, Int.cast_sum, Int.cast_mul]
  · intro j
    rfl

end Hindman168

