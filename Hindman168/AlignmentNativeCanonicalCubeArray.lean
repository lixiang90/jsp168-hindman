import Hindman168.AlignmentNativeModelLogPolynomial
import Hindman168.AlignmentCubeArrayExponent

namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three
  alignmentAddingPairFintype

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

variable (n : ℕ) (u : Fin (n + 1) → AlignmentAddingPair N i → ℤ)
  (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))

noncomputable def alignmentNativeCanonicalCubeArray (g b : G) (t : Fin N → ℕ)
    (M : ℕ) (rho : AlignmentAddingPair N i → ℕ) (delta : AlignmentAddingPair N i → ℤ)
    (T : Finset (Fin N)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (v : AlignmentAddingPair N i → ℤ) :
    alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu :=
  alignmentNativeModelArray n u hu g b
    (alignmentCubeVertex M (alignmentNaturalBlockProduct t T) p Y ell inc weight + Y +
      (alignmentPivotArrayResidue t T M p 0 +
        (alignmentNaturalBlockProduct t T : ℤ) * alignmentIntegerSlotShift rho v -
        alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift rho v)) / (M : ℤ))
    (fun e => if e.targetTail = T then delta e else 0)

theorem alignmentNativeCanonicalCubeArray_evaluation (g b : G) (t : Fin N → ℕ)
    (M : ℕ) (hM : 0 < M)
    (rho : AlignmentAddingPair N i → ℕ) (delta : AlignmentAddingPair N i → ℤ)
    (T : Finset (Fin N)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (v z : AlignmentAddingPair N i → ℤ) :
    (alignmentNativeCanonicalCubeArray n u hu g b t M rho delta T p Y ell inc weight v).val z =
      g ^ (alignmentIntegerArrayArgument t M rho delta T
        (p + (M : ℤ) * (ell + ∑ j, weight j * inc j)) v z / (M : ℤ)) * b := by
  rw [alignmentIntegerArrayArgument_cube_quotient t M hM (Y := Y)]
  unfold alignmentNativeCanonicalCubeArray
  simp only [alignmentNativeModelArray, alignmentIntegerArrayProgression, mul_ite, mul_zero]

end Hindman168
