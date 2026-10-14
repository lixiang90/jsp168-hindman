import Hindman168.NativeCenterLayerCoordinates
import Hindman168.NativeCenterQuotientNormedModel
import Hindman168.QuotientSectionRetraction
import Hindman168.NativeOrderedExponentialSmooth

/-! A global smooth function recovers the true lattice center coordinates
on every genuinely central original group element. Its construction uses
the true original logarithm and an actual continuous linear retraction. -/

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_layer_coordinates_contMDiff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ)
      I ∞ (fun x => (nativeCenterLayerCoordinates (I := I) Γ x : G)) := by
  have he : (fun x => (nativeCenterLayerCoordinates (I := I) Γ x : G)) =
      nativeOrderedExponentialCoordinates (I := I) (G := G)
        (fun i => (nativeCenterLayerRealBasis (I := I) Γ i).val) :=
    funext (native_center_layer_coordinates_ordered_product (I := I) Γ)
  rw [he]
  exact native_ordered_exponential_coordinates_contMDiff (I := I) (G := G) _

noncomputable def nativeCenterLayerCoordinateRecovery (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ :=
  (nativeCenterLayerRealBasis (I := I) Γ).equivFunL
    (finiteRealQuotientSectionRetraction (nativeLieCenterModel (I := I) (G := G))
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))

theorem native_center_layer_coordinate_recovery_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    nativeCenterLayerCoordinateRecovery (I := I) Γ (nativeCenterLayerCoordinates (I := I) Γ x : G) = x := by
  unfold nativeCenterLayerCoordinateRecovery
  rw [native_center_layer_coordinates_exponential, nativeLieGlobalLogarithm_exponential,
    finiteRealQuotientSectionRetraction_subtype]
  exact (nativeCenterLayerRealBasis (I := I) Γ).equivFun.apply_symm_apply x

theorem native_center_layer_coordinate_recovery_right (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) (hg : g ∈ Subgroup.center G) :
    (nativeCenterLayerCoordinates (I := I) Γ (nativeCenterLayerCoordinateRecovery (I := I) Γ g) : G) = g := by
  obtain ⟨x, hx⟩ := (nativeCenterLayerCoordinates (I := I) Γ).surjective ⟨g, hg⟩
  have he : (nativeCenterLayerCoordinates (I := I) Γ x : G) = g := congrArg Subtype.val hx
  rw [← he, native_center_layer_coordinate_recovery_coordinates]

theorem native_center_layer_coordinate_recovery_contMDiff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) ∞
      (nativeCenterLayerCoordinateRecovery (I := I) Γ) := by
  let P := finiteRealQuotientSectionRetraction (nativeLieCenterModel (I := I) (G := G))
  have hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, nativeLieCenterModel (I := I) (G := G)) ∞ P :=
    P.contDiff.contMDiff
  exact (nativeCenterLayerRealBasis (I := I) Γ).equivFunL.contDiff.contMDiff.comp
    (hP.comp (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I)))

end Hindman168
