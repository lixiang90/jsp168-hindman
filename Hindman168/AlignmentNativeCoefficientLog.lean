import Hindman168.AlignmentNativeArrayTranslationCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → σ → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

noncomputable def alignmentNativeCoefficientLog
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) :=
  alignmentNativeArrayModelCoefficients n u hu
    ((alignmentNativeArrayExponentialHomeomorph n u hu).symm a)

theorem alignmentNativeCoefficientLog_evaluation
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) (z : σ → ℤ) :
    alignmentLiePolynomialArraysEvaluation (fun j => (z j : ℝ))
        (alignmentNativeCoefficientLog n u hu a) =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (a.val z) := by
  have h := alignmentNativeArrayExponential_evaluation n u hu
    ((alignmentNativeArrayExponentialHomeomorph n u hu).symm a) z
  rw [(alignmentNativeArrayExponentialHomeomorph n u hu).apply_symm_apply] at h
  rw [h, nativeLieGlobalLogarithm_exponential]
  rfl

noncomputable def alignmentNativeSelectedEvaluation :
    alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) →ₗ[ℝ] (Fin (n + 1) → E) :=
  LinearMap.pi (fun j => (alignmentLiePolynomialArraysEvaluation (fun k => (u j k : ℝ))).toLinearMap)

include hu in
omit [FiniteDimensional ℝ E] [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem alignmentNativeSelectedEvaluation_injective :
    Function.Injective (alignmentNativeSelectedEvaluation (E := E) (I := I) (G := G) n u) := by
  intro x y h
  apply hu
  apply nativeFiniteProductCoordinate_injective n
  funext j
  exact (alignmentNativeFiniteEvaluation_coordinate n u x j).trans
    ((congrFun h j).trans (alignmentNativeFiniteEvaluation_coordinate n u y j).symm)

noncomputable def alignmentNativeCoefficientRecovery :
    (Fin (n + 1) → E) →ₗ[ℝ] alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G) :=
  (alignmentNativeSelectedEvaluation (E := E) (I := I) (G := G) n u).leftInverse

include hu in
omit [FiniteDimensional ℝ E] [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem alignmentNativeCoefficientRecovery_left
    (x : alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra I G)) :
    alignmentNativeCoefficientRecovery (I := I) (G := G) n u
      (alignmentNativeSelectedEvaluation (I := I) (G := G) n u x) = x := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (alignmentNativeSelectedEvaluation_injective n u hu)) x

theorem alignmentNativeCoefficientRecovery_log
    (a : alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) :
    alignmentNativeCoefficientRecovery (I := I) (G := G) n u
      (fun j => nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (a.val (u j))) =
        alignmentNativeCoefficientLog n u hu a := by
  have h : (fun j => nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (a.val (u j))) =
      alignmentNativeSelectedEvaluation (I := I) (G := G) n u (alignmentNativeCoefficientLog n u hu a) := by
    funext j
    exact (alignmentNativeCoefficientLog_evaluation n u hu a (u j)).symm
  rw [h, alignmentNativeCoefficientRecovery_left n u hu]

end Hindman168

