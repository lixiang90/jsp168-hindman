import Hindman168.NativeCentralSubspaceLieIdeal
import Hindman168.NativeRationalCompactRepresentatives
import Hindman168.NormalQuotientLatticeDiscreteness
import Hindman168.NormalQuotientLatticeCocompactness

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem nativeCentralSubspaceQuotient_lattice_image_discrete (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    DiscreteTopology (Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV))) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : LocallyCompactSpace G := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  let N := nativeCentralSubspaceSubgroup (I := I) V hV
  letI : IsClosed (N : Set G) := nativeCentralSubspaceSubgroup_closed V hV
  obtain ⟨K, hK, hsub, hrep⟩ := nativeRationalLieSubalgebra_compact_representatives Γ
    (nativeCentralSubspaceLieIdeal (I := I) V hV).toLieSubalgebra hrat
  rw [nativeCentralSubspaceLieIdeal_subgroup] at hsub hrep
  apply normalQuotient_lattice_image_discrete Γ N hK hsub
  intro g hg
  obtain ⟨x, hx, γ, hγ, he⟩ := hrep g hg
  have hγN : γ ∈ N := by
    have h := N.mul_mem (N.inv_mem (hsub hx)) hg
    rw [he] at h
    simpa only [inv_mul_cancel_left] using h
  exact Set.mem_mul.mpr ⟨x, hx, γ, ⟨hγ, hγN⟩, he.symm⟩

omit [Module ℚ E] in
theorem nativeCentralSubspaceQuotient_lattice_image_cocompact (Γ : Subgroup G)
    [CompactSpace (G ⧸ Γ)] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    CompactSpace ((G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) ⧸
      Γ.map (QuotientGroup.mk' (nativeCentralSubspaceSubgroup (I := I) V hV))) :=
  normalQuotient_lattice_image_cocompact Γ (nativeCentralSubspaceSubgroup (I := I) V hV)

end Hindman168
