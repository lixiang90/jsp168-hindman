import Hindman168.AlignmentNativeCoefficientLog
import Hindman168.NativeFiniteOrbitLogProjection

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ θ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

noncomputable def alignmentNativeArrayLogPolynomial (g b : Fin (n + 1) → G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : Fin (n + 1) → MvPolynomial θ ℝ) : MvPolynomial θ ℝ :=
  nativeFiniteOrbitLogProjection (I := I) g b
    (ell.comp (alignmentNativeCoefficientRecovery (I := I) (G := G) n u)) P

theorem alignmentNativeArrayLogPolynomial_degree (g b : Fin (n + 1) → G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : Fin (n + 1) → MvPolynomial θ ℝ) (s d : ℕ)
    (hs : Group.nilpotencyClass G ≤ s) (hP : ∀ j, (P j).totalDegree ≤ d) :
    (alignmentNativeArrayLogPolynomial n u g b ell P).totalDegree ≤ ((s * s + 1) ^ (s + 1)) * d :=
  nativeFiniteOrbitLogProjection_degree _ _ _ _ s d hs hP

theorem alignmentNativeArrayLogPolynomial_eval (g b : Fin (n + 1) → G)
    (ell : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] ℝ)
    (P : Fin (n + 1) → MvPolynomial θ ℝ) (z : θ → ℝ) (k : Fin (n + 1) → ℤ)
    (hk : ∀ j, MvPolynomial.eval z (P j) = (k j : ℝ))
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu)
    (ha : ∀ j, a.val (u j) = g j ^ k j * b j) :
    MvPolynomial.eval z (alignmentNativeArrayLogPolynomial n u g b ell P) =
      ell (alignmentNativeCoefficientLog n u hu a) := by
  rw [alignmentNativeArrayLogPolynomial, nativeFiniteOrbitLogProjection_eval _ _ _ _ z k hk]
  simp only [LinearMap.comp_apply]
  simp_rw [← ha]
  rw [alignmentNativeCoefficientRecovery_log n u hu]

end Hindman168

