import Hindman168.BasisLayerCoordinates
import Hindman168.NativeCenterLayerCoordinates
import Hindman168.NativeGroupLowerCentralExact

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_layer_mem_iff_zero_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ)
    (v : nativeLieCenterModel (I := I) (G := G)) :
    v.val ∈ nativeLieLowerCentralModel (I := I) (G := G) j ↔
      ∀ i, (nativeCenterLayerRealBasis (I := I) Γ i).val ∉
        nativeLieLowerCentralModel (I := I) (G := G) j →
          (nativeCenterLayerRealBasis (I := I) Γ).repr v i = 0 :=
  basis_layer_mem_iff_zero_coordinates (nativeCenterLayerRealBasis (I := I) Γ) _ _
    (native_center_layer_real_basis_adapted Γ j) v

theorem native_center_layer_synthesis_mem_iff_zero_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ)
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    ((nativeCenterLayerRealBasis (I := I) Γ).equivFun.symm x).val ∈
      nativeLieLowerCentralModel (I := I) (G := G) j ↔
        ∀ i, (nativeCenterLayerRealBasis (I := I) Γ i).val ∉
          nativeLieLowerCentralModel (I := I) (G := G) j → x i = 0 := by
  rw [native_center_layer_mem_iff_zero_coordinates Γ j]
  change (∀ i, _ → ((nativeCenterLayerRealBasis (I := I) Γ).equivFun
    ((nativeCenterLayerRealBasis (I := I) Γ).equivFun.symm x)) i = 0) ↔ _
  rw [LinearEquiv.apply_symm_apply]

theorem native_center_layer_coordinates_group_layer_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (j : ℕ)
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLayerCoordinates (I := I) Γ x : G) ∈ (⊤ : Subgroup G).lowerCentralSeries j ↔
      ∀ i, (nativeCenterLayerRealBasis (I := I) Γ i).val ∉
        nativeLieLowerCentralModel (I := I) (G := G) j → x i = 0 := by
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I),
    nativeLieLowerCentralSubgroup_mem_globalLogarithm_iff, native_center_layer_coordinates_exponential,
    nativeLieGlobalLogarithm_exponential]
  exact native_center_layer_synthesis_mem_iff_zero_coordinates Γ j x

end Hindman168
