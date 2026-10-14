import Hindman168.AlignmentNativeCanonicalCubeArray

/-! The actual residue correction fixes the base exponent of the SAME
point orbit used by every cube vertex. The integer origin Y cancels exactly. -/
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

noncomputable def alignmentCanonicalPointExponent {N : ℕ} {i : Fin N}
    (t : Fin N → ℕ) (M : ℕ) (rho : AlignmentAddingPair N i → ℕ)
    (T : Finset (Fin N)) (p : ℤ) (shift : AlignmentAddingPair N i → ℤ) : ℤ :=
  (alignmentNaturalBlockProduct t T : ℤ) * p / (M : ℤ) +
    (alignmentPivotArrayResidue t T M p 0 +
      (alignmentNaturalBlockProduct t T : ℤ) * alignmentIntegerSlotShift rho shift -
      alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift rho shift)) / (M : ℤ)

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G]
  [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [BoundarylessManifold I G]
  [T2Space G] [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G]
  (n : ℕ) (v : Fin (n+1) → AlignmentAddingPair N i → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n v))

theorem alignment_native_canonical_cube_point_orbit
    (g a : G) (t : Fin N → ℕ) (M : ℕ)
    (rho : AlignmentAddingPair N i → ℕ) (delta : AlignmentAddingPair N i → ℤ)
    (T : Finset (Fin N)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (shift : AlignmentAddingPair N i → ℤ) :
    alignmentNativeCanonicalCubeArray n v hv g a t M rho delta T p Y ell inc weight shift =
      alignmentNativeModelOrbit n v hv g a
        (alignmentCanonicalPointExponent t M rho T p shift)
        (alignmentNaturalBlockProduct t T)
        (fun e => if e.targetTail = T then delta e else 0)
        (ell + ∑ j, weight j * inc j) := by
  rw [alignmentNativeCanonicalCubeArray, alignmentCubeVertex_affine]
  unfold alignmentNativeModelOrbit alignmentCubeBase alignmentCanonicalPointExponent
  congr 1
  ring

theorem alignment_native_canonical_cube_origin_independent
    (g a : G) (t : Fin N → ℕ) (M : ℕ)
    (rho : AlignmentAddingPair N i → ℕ) (delta : AlignmentAddingPair N i → ℤ)
    (T : Finset (Fin N)) (p Y Y' ell : ℤ) (inc weight : κ → ℤ)
    (shift : AlignmentAddingPair N i → ℤ) :
    alignmentNativeCanonicalCubeArray n v hv g a t M rho delta T p Y ell inc weight shift =
      alignmentNativeCanonicalCubeArray n v hv g a t M rho delta T p Y' ell inc weight shift := by
  rw [alignment_native_canonical_cube_point_orbit, alignment_native_canonical_cube_point_orbit]

end Hindman168

