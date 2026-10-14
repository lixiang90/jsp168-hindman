import Hindman168.NativeTerminalCentralSubspace
import Hindman168.NativeCentralSubspaceQuotientLattice
import Hindman168.NativeCentralSubspaceLayerLatticeLift

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem nativeLattice_terminal_central_quotient_exists [Nontrivial E] (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ∃ j : ℕ, ∃ hV : nativeLieLowerCentralModel (I := I) (G := G) j ≤
        nativeLieCenterModel (I := I) (G := G),
      let V := nativeLieLowerCentralModel (I := I) (G := G) j
      let N := nativeCentralSubspaceSubgroup (I := I) V hV
      let q := QuotientGroup.mk' N
      V ≠ ⊥ ∧ Module.finrank ℝ (E ⧸ V) < Module.finrank ℝ E ∧
        DiscreteTopology (Γ.map q) ∧ CompactSpace ((G ⧸ N) ⧸ Γ.map q) ∧
        ∀ k ≤ j, (Γ ⊓ (⊤ : Subgroup G).lowerCentralSeries k).map q =
          Γ.map q ⊓ (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries k := by
  obtain ⟨j, hj, _, hV, hrat, hprior, hdim⟩ :=
    nativeLattice_terminal_central_subspace_exists (I := I) Γ
  exact ⟨j, hV, hj, hdim,
    nativeCentralSubspaceQuotient_lattice_image_discrete Γ _ hV hrat,
    nativeCentralSubspaceQuotient_lattice_image_cocompact Γ _ hV,
    fun k hk => nativeCentralSubspaceQuotient_lattice_layer_image Γ _ hV k (hprior k hk)⟩

end Hindman168
