import Hindman168.NativeLatticeFilteredLayerDimensions
import Hindman168.RoughNativeStretchedFiltration
import Hindman168.RoughNativeStretchedLieTerminal

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughFilteredLayerStart (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) : ℕ :=
  nativeLatticeFilteredLayerStart (I := I) Γ ((i ⌈/⌉ D)-1)

theorem rough_filtered_smooth_basis_adapted (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    roughFilteredLayerStart (I := I) Γ D i ≤ Module.finrank ℝ E ∧
      (∀ k, nativeLatticeFilteredSmoothRealBasis (I := I) Γ k ∈
        roughNativeStretchedLieFiltration (I := I) (G := G) D i ↔
          roughFilteredLayerStart (I := I) Γ D i ≤ k.val) ∧
      Submodule.span ℝ (nativeLatticeFilteredSmoothRealBasis (I := I) Γ ''
        {k | roughFilteredLayerStart (I := I) Γ D i ≤ k.val}) =
          roughNativeStretchedLieFiltration (I := I) (G := G) D i :=
  native_lattice_filtered_layer_start_spec (I := I) Γ _

theorem rough_filtered_smooth_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) (k : Fin (Module.finrank ℝ E)) :
    nativeLieExponential (I := I) (G := G) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ k) ∈
      roughStretchedLowerCentralFiltration G D i ↔ roughFilteredLayerStart (I := I) Γ D i ≤ k.val :=
  (rough_native_stretched_filtration_exp_mem_iff (I := I) D i _).trans
    ((native_lattice_filtered_layer_start_spec (I := I) Γ _).2.1 k)

theorem rough_filtered_layer_start_monotone (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D : ℕ) (hD : 0 < D) :
    Monotone (roughFilteredLayerStart (I := I) Γ D) := by
  intro i j hij
  exact native_lattice_filtered_layer_start_monotone (I := I) Γ
    (Nat.sub_le_sub_right (rough_ceiling_index_monotone D hD hij) 1)

theorem rough_filtered_layer_start_eq_codimension (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D i : ℕ) :
    roughFilteredLayerStart (I := I) Γ D i = Module.finrank ℝ E -
      Module.finrank ℝ (roughNativeStretchedLieFiltration (I := I) (G := G) D i) :=
  native_lattice_filtered_layer_start_eq_codimension (I := I) Γ _

end Hindman168
