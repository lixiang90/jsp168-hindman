import Hindman168.AlignmentNativeArrayCompact
import Hindman168.PointwiseArrayNilpotence
import Hindman168.FinitePiLatticeNilpotence

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

noncomputable abbrev alignmentNativeJointArrayGroup :=
  ∀ i, alignmentNativeAllIntegerArrayGroup (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)

noncomputable def alignmentNativeJointArrayLattice (Γ : ∀ i, Subgroup (G i)) :
    Subgroup (alignmentNativeJointArrayGroup n u hu) :=
  Subgroup.pi Set.univ (fun i => pointwiseArrayLattice
    (alignmentNativeAllIntegerArrayGroup (E := E i) (I := I i) (G := G i) (n i) (u i) (hu i)) (Γ i))

theorem alignmentNativeJointArrayLattice_mem (Γ : ∀ i, Subgroup (G i))
    (a : alignmentNativeJointArrayGroup n u hu) :
    a ∈ alignmentNativeJointArrayLattice n u hu Γ ↔ ∀ i z, (a i).val z ∈ Γ i := by
  simp only [alignmentNativeJointArrayLattice, Subgroup.mem_pi, Set.mem_univ, forall_const,
    pointwiseArrayLattice_mem]

theorem alignmentNativeJointArrayLattice_discrete [Finite ι]
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)] :
    DiscreteTopology (alignmentNativeJointArrayLattice n u hu Γ) := by
  letI := fun i => alignmentNativeArrayLattice_discrete (n i) (u i) (hu i) (Γ i)
  exact finitePiSubgroup_discrete _

theorem alignmentNativeJointArrayGroup_lowerCentral_bot (s : ℕ)
    (hs : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (alignmentNativeJointArrayGroup n u hu)).lowerCentralSeries s = ⊥ := by
  apply piGroup_lowerCentral_bot
  intro i
  exact pointwiseArraySubgroup_lowerCentral_bot _ s (hs i)

theorem alignmentNativeJointArrayGroup_nilpotencyClass_le (s : ℕ)
    (hs : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥) :
    Group.nilpotencyClass (alignmentNativeJointArrayGroup n u hu) ≤ s := by
  apply piGroup_nilpotencyClass_le
  intro i
  exact pointwiseArraySubgroup_lowerCentral_bot _ s (hs i)

theorem alignmentNativeJointArrayCoset_compact [∀ i, Module ℚ (E i)]
    (Γ : ∀ i, Subgroup (G i)) [∀ i, DiscreteTopology (Γ i)] [∀ i, CompactSpace (G i ⧸ Γ i)] :
    CompactSpace (alignmentNativeJointArrayGroup n u hu ⧸ alignmentNativeJointArrayLattice n u hu Γ) := by
  letI : ∀ i, IsTopologicalGroup (G i) := fun i => topologicalGroup_of_lieGroup (I i) ∞
  letI := fun i => alignmentNativeArrayLattice_quotient_compact (n i) (u i) (hu i) (Γ i)
  exact piCoset_quotient_compact _

end Hindman168
