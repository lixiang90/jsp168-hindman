import Hindman168.NativeCenterLatticeCoordinates
import Hindman168.NativeCenterQuotientNormedModel
import Hindman168.QuotientSectionRetraction

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

noncomputable def nativeCenterCoordinateRecovery (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ :=
  (nativeCenterLatticeRealBasis (I := I) Γ).equivFunL
    (finiteRealQuotientSectionRetraction (nativeLieCenterModel (I := I) (G := G))
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))

theorem native_center_coordinate_recovery_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    nativeCenterCoordinateRecovery (I := I) Γ (nativeCenterLatticeCoordinates (I := I) Γ x : G) = x := by
  unfold nativeCenterCoordinateRecovery
  rw [native_center_lattice_coordinates_exponential, nativeLieGlobalLogarithm_exponential,
    finiteRealQuotientSectionRetraction_subtype]
  exact (nativeCenterLatticeRealBasis (I := I) Γ).equivFun.apply_symm_apply x

theorem native_center_coordinate_recovery_right (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) (hg : g ∈ Subgroup.center G) :
    (nativeCenterLatticeCoordinates (I := I) Γ (nativeCenterCoordinateRecovery (I := I) Γ g) : G) = g := by
  obtain ⟨x, hx⟩ := (nativeCenterLatticeCoordinates (I := I) Γ).surjective ⟨g, hg⟩
  have he : (nativeCenterLatticeCoordinates (I := I) Γ x : G) = g := congrArg Subtype.val hx
  rw [← he, native_center_coordinate_recovery_coordinates]

theorem native_center_coordinate_recovery_contMDiff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) ∞
      (nativeCenterCoordinateRecovery (I := I) Γ) := by
  let P := finiteRealQuotientSectionRetraction (nativeLieCenterModel (I := I) (G := G))
  have hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, nativeLieCenterModel (I := I) (G := G)) ∞ P :=
    P.contDiff.contMDiff
  exact (nativeCenterLatticeRealBasis (I := I) Γ).equivFunL.contDiff.contMDiff.comp
    (hP.comp (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I)))

end Hindman168
