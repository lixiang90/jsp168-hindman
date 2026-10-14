import Hindman168.AlignmentNativeJointLieGroup
import Hindman168.AlignmentNativeJointTranslations
import Hindman168.AlignmentNativeArrayCosetSmooth

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

theorem alignmentNativeJointArrayTranslation_contMDiff (v : ∀ i, σ i → ℤ) :
    letI := alignmentNativeJointChartedSpace n u hu
    let J := 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeJointArrayTranslation n u hu v) := by
  letI := fun i => alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  exact finitePiGroup_map_contMDiff
    (fun i => alignmentNativeArrayExponentialDiffeomorph (n i) (u i) (hu i))
    (fun i => alignmentNativeArrayTranslation (n i) (u i) (hu i) (v i))
    (fun i => alignmentNativeArrayTranslation_contMDiff (n i) (u i) (hu i) (v i))

variable (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)]

@[reducible]
noncomputable def alignmentNativeJointCosetChartedSpace :
    ChartedSpace (alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
      (alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) := by
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup (alignmentNativeJointArrayGroup n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  exact discreteCosetGlobalChartedSpace (alignmentNativeJointDiffeomorph n u hu)
    (alignmentNativeJointArrayLattice n u hu Γ)

theorem alignmentNativeJointCoset_isManifold :
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    IsManifold 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
      (alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) := by
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup (alignmentNativeJointArrayGroup n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  exact discreteCosetGlobal_isManifold (alignmentNativeJointDiffeomorph n u hu)
    (alignmentNativeJointArrayLattice n u hu Γ)

theorem alignmentNativeJointCosetProjection_contMDiff :
    letI := alignmentNativeJointChartedSpace n u hu
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (QuotientGroup.mk (s := alignmentNativeJointArrayLattice n u hu Γ)) := by
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup (alignmentNativeJointArrayGroup n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  exact discreteCosetProjection_contMDiff (alignmentNativeJointDiffeomorph n u hu)
    (alignmentNativeJointArrayLattice n u hu Γ)

theorem alignmentNativeJointCosetEvaluation_contMDiff (i : ι) (z : σ i → ℤ) :
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    letI := nativeDiscreteCosetChartedSpace (E := E i) (I := I i) (Γ i)
    ContMDiff 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) 𝓘(ℝ, E i) ∞
      (alignmentNativeJointCosetEvaluation n u hu Γ i z) := by
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup (alignmentNativeJointArrayGroup n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  letI := nativeDiscreteCosetChartedSpace (E := E i) (I := I i) (Γ i)
  letI := alignmentNativeArrayChartedSpace (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)
  apply discreteCoset_contMDiff_of_projection (alignmentNativeJointDiffeomorph n u hu)
    (alignmentNativeJointArrayLattice n u hu Γ)
  exact (nativeDiscreteCoset_projection_contMDiff (E := E i) (I := I i) (Γ i)).comp
    ((alignmentNativeArray_evaluation_contMDiff (n i) (u i) (hu i) z).comp
      (alignmentNativeJoint_coordinate_contMDiff n u hu i))

theorem alignmentNativeJointCosetTranslation_contMDiff (v : ∀ i, σ i → ℤ) :
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
    ContMDiff J J ∞ (alignmentNativeJointCosetTranslation n u hu Γ v) := by
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup (alignmentNativeJointArrayGroup n u hu) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u) ∞
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  letI := alignmentNativeJointCosetChartedSpace n u hu Γ
  apply discreteCoset_contMDiff_of_projection (alignmentNativeJointDiffeomorph n u hu)
    (alignmentNativeJointArrayLattice n u hu Γ)
  exact (alignmentNativeJointCosetProjection_contMDiff n u hu Γ).comp
    (alignmentNativeJointArrayTranslation_contMDiff n u hu v)

noncomputable def alignmentNativeJointCosetTranslationDiffeomorph (v : ∀ i, σ i → ℤ) :
    letI := alignmentNativeJointCosetChartedSpace n u hu Γ
    let J := 𝓘(ℝ, alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u)
    let Q := alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ
    Diffeomorph J J Q Q ∞ := by
  letI := alignmentNativeJointCosetChartedSpace n u hu Γ
  exact
    { toEquiv := (alignmentNativeJointCosetTranslationHomeomorph n u hu Γ v).toEquiv
      contMDiff_toFun := alignmentNativeJointCosetTranslation_contMDiff n u hu Γ v
      contMDiff_invFun := alignmentNativeJointCosetTranslation_contMDiff n u hu Γ (-v) }

end Hindman168
