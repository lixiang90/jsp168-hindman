import Hindman168.NativeRationalLatticeCompact

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeSubgroup_logSpan_rational_intersection
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hK : K ≤ Γ)
    (V : Submodule ℝ E)
    (hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (K : Set G)) = V) :
    V.restrictScalars ℚ ⊓ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ =
      nativeSubgroupRationalLogSpan (E := E) (I := I) K := by
  have hU : nativeSubgroupRationalLogSpan (E := E) (I := I) K ≤
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    nativeSubgroupRationalLogSpan_le_of_logarithms_mem K _
      (fun g hg => nativeSubgroup_logarithm_mem_span Γ (hK hg))
  have h := nativeLattice_rationalSubspace_realSpan_intersection (E := E) (I := I) Γ _ hU
  rw [nativeSubgroupRationalLogSpan_real_span_eq, hspan] at h
  exact h

theorem nativeSubgroup_logSpan_rational
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hK : K ≤ Γ)
    (V : Submodule ℝ E)
    (hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (K : Set G)) = V) :
    nativeLatticeRationalSubspace (E := E) (I := I) Γ V := by
  unfold nativeLatticeRationalSubspace
  rw [nativeSubgroup_logSpan_rational_intersection Γ K hK V hspan,
    nativeSubgroupRationalLogSpan_real_span_eq, hspan]

theorem nativeSubgroup_logSpan_covers_lattice_roots
    (Γ K : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hK : K ≤ Γ)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (K : Set G)) =
      nativeLieSubalgebraModel (E := E) S) :
    Γ ⊓ nativeLieSubalgebraSubgroup (E := E) S ≤ nativeSubgroupRationalHull (E := E) (I := I) K := by
  intro g hg
  apply (nativeSubgroupRationalHull_mem_iff K g).mpr
  rw [← nativeSubgroup_logSpan_rational_intersection Γ K hK _ hspan]
  exact ⟨(nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S g).mp hg.2,
    nativeSubgroup_logarithm_mem_span Γ hg.1⟩

end Hindman168

