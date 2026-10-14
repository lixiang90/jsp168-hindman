import Hindman168.FinitePiGroupLie
import Hindman168.AlignmentNativeJointArrayGroup
import Hindman168.AlignmentNativeArrayLieGroup

namespace Hindman168
open scoped Manifold ContDiff BigOperators

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {ι : Type*} {σ E H G : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
  [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] [∀ i, Group (G i)]
  [∀ i, LieGroup (I i) ∞ (G i)] [∀ i, BoundarylessManifold (I i) (G i)]
  [∀ i, T2Space (G i)] [∀ i, Group.IsNilpotent (G i)]
  [∀ i, ConnectedSpace (G i)] [∀ i, SimplyConnectedSpace (G i)]
  (n : ι → ℕ) (u : ∀ i, Fin (n i + 1) → σ i → ℤ)
  (hu : ∀ i, Function.Injective (alignmentNativeFiniteEvaluation (E := E i) (I := I i) (G := G i) (n i) (u i)))

variable [Fintype ι]

noncomputable abbrev alignmentNativeJointLieModel :=
  ∀ i, alignmentNativeFiniteImageModel (E := E i) (I := I i) (G := G i) (n i) (u i)

@[reducible]
noncomputable def alignmentNativeJointChartedSpace :
    ChartedSpace (alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) (alignmentNativeJointArrayGroup n u hu) := by
  letI := fun i => alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  exact finitePiGroupChartedSpace (fun i => alignmentNativeArrayExponentialDiffeomorph (n i) (u i) (hu i))

noncomputable def alignmentNativeJointDiffeomorph :
    letI := alignmentNativeJointChartedSpace n u hu
    let J := 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
    Diffeomorph J J (alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) (alignmentNativeJointArrayGroup n u hu) ∞ := by
  letI := fun i => alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  exact finitePiGroupDiffeomorph (fun i => alignmentNativeArrayExponentialDiffeomorph (n i) (u i) (hu i))

theorem alignmentNativeJoint_lieGroup :
    letI := alignmentNativeJointChartedSpace n u hu
    LieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞ (alignmentNativeJointArrayGroup n u hu) := by
  letI := fun i => alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  letI := fun i => alignmentNativeArray_lieGroup (n i) (u i) (hu i)
  exact finitePiGroup_lieGroup (fun i => alignmentNativeArrayExponentialDiffeomorph (n i) (u i) (hu i))

theorem alignmentNativeJoint_coordinate_contMDiff (i : ι) :
    letI := alignmentNativeJointChartedSpace n u hu
    letI := alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
    ContMDiff 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
      𝓘(ℝ, alignmentNativeFiniteImageModel (E := E i) (I := I i) (G := G i) (n i) (u i)) ∞
      (fun a : alignmentNativeJointArrayGroup n u hu => a i) := by
  letI := fun i => alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  exact finitePiGroup_coordinate_contMDiff
    (fun i => alignmentNativeArrayExponentialDiffeomorph (n i) (u i) (hu i)) i

end Hindman168

