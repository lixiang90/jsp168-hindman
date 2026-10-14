import Hindman168.AlignmentNativeJointLieGroup
import Hindman168.NativeNilmanifoldConstruction

namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe v

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {ι : Type v} {σ E H G : ι → Type v}
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

theorem alignmentNativeJoint_contractible : ContractibleSpace (alignmentNativeJointArrayGroup n u hu) := by
  letI := alignmentNativeJointChartedSpace n u hu
  exact (alignmentNativeJointDiffeomorph n u hu).toHomeomorph.symm.contractibleSpace

noncomputable def alignmentNativeJointNilmanifold [∀ i, Module ℚ (E i)]
    (s : ℕ) (hs : ∀ i, Group.nilpotencyClass (G i) ≤ s)
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)] [∀ i, CompactSpace (G i ⧸ Γ i)] :
    NativeNilmanifoldData.{v} s := by
  let V := alignmentNativeJointLieModel (E := E) (I := I) (G := G) n u
  let A := alignmentNativeJointArrayGroup n u hu
  letI := alignmentNativeJointChartedSpace n u hu
  letI := alignmentNativeJoint_lieGroup n u hu
  letI : IsTopologicalGroup A := topologicalGroup_of_lieGroup 𝓘(ℝ, V) ∞
  letI := alignmentNativeJoint_contractible n u hu
  letI : SimplyConnectedSpace A := inferInstance
  letI := alignmentNativeJointArrayLattice_discrete n u hu Γ
  letI := alignmentNativeJointArrayCoset_compact n u hu Γ
  letI : Module ℚ V := Module.compHom _ (Rat.castHom ℝ)
  have hcut : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥ :=
    fun i => Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (hs i)
  letI : Group.IsNilpotent A := Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s, alignmentNativeJointArrayGroup_lowerCentral_bot n u hu s hcut⟩
  exact nativeNilmanifoldOfLie (E := V) (I := 𝓘(ℝ, V)) (G := A) s
    (alignmentNativeJointArrayGroup_nilpotencyClass_le n u hu s hcut)
    (alignmentNativeJointArrayLattice n u hu Γ)

theorem alignmentNativeJointNilmanifold_group [∀ i, Module ℚ (E i)]
    (s : ℕ) (hs : ∀ i, Group.nilpotencyClass (G i) ≤ s)
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)] [∀ i, CompactSpace (G i ⧸ Γ i)] :
    (alignmentNativeJointNilmanifold n u hu s hs Γ).G = alignmentNativeJointArrayGroup n u hu := rfl

theorem alignmentNativeJointNilmanifold_lattice [∀ i, Module ℚ (E i)]
    (s : ℕ) (hs : ∀ i, Group.nilpotencyClass (G i) ≤ s)
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)] [∀ i, CompactSpace (G i ⧸ Γ i)] :
    (alignmentNativeJointNilmanifold n u hu s hs Γ).Γ = alignmentNativeJointArrayLattice n u hu Γ := rfl

end Hindman168
