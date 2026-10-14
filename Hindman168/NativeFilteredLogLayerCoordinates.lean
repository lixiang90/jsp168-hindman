import Hindman168.NativeLatticeFilteredDiffeomorph
import Hindman168.BasisLayerCoordinates
import Hindman168.NativeGroupLowerCentralExact
import Hindman168.RoughNativeStretchedFiltration

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_filtered_lie_layer_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (k : ℕ) (v : E) :
    v ∈ nativeLieLowerCentralModel (I := I) (G := G) k ↔
      ∀ i, i.val < nativeLatticeFilteredLayerStart (I := I) Γ k →
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr v i = 0 := by
  have h := basis_layer_mem_iff_zero_coordinates (nativeLatticeFilteredSmoothRealBasis (I := I) Γ)
    (fun i => nativeLatticeFilteredLayerStart (I := I) Γ k ≤ i.val) _
    (native_lattice_filtered_layer_start_spec (I := I) Γ k).2.2 v
  simpa only [not_le] using h

theorem native_filtered_group_layer_mem_iff_log_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (k : ℕ) (g : G) :
    g ∈ (⊤ : Subgroup G).lowerCentralSeries k ↔
      ∀ i, i.val < nativeLatticeFilteredLayerStart (I := I) Γ k →
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
          (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) i = 0 := by
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I),
    nativeLieLowerCentralSubgroup_mem_globalLogarithm_iff,
    native_filtered_lie_layer_mem_iff_coordinates (I := I) Γ]

theorem rough_filtered_group_mem_iff_log_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (D k : ℕ) (g : G) :
    g ∈ roughStretchedLowerCentralFiltration G D k ↔
      ∀ i, i.val < nativeLatticeFilteredLayerStart (I := I) Γ ((k ⌈/⌉ D)-1) →
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
          (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) i = 0 := by
  rw [rough_native_stretched_filtration_mem_log_iff (I := I),
    native_filtered_lie_layer_mem_iff_coordinates (I := I) Γ]

end Hindman168
