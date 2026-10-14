import Hindman168.NativeCentralSubspaceLatticeCoordinates
import Hindman168.NativeCentralSubspaceQuotientCharted
import Hindman168.QuotientSectionRetraction

/-! A global smooth function recovers the true lattice central-subspace coordinates
on every original group element in the specified subgroup. Its construction uses
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
attribute [local instance] nativeCentralSubspaceSubgroup_normal

noncomputable def nativeCentralSubspaceCoordinateRecovery (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) (g : G) :
    Fin (Module.finrank ℝ (V)) → ℝ :=
  (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFunL
    (finiteRealQuotientSectionRetraction (V)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))

theorem native_central_subspace_coordinate_recovery_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (x : Fin (Module.finrank ℝ (V)) → ℝ) :
    nativeCentralSubspaceCoordinateRecovery (I := I) Γ V hV hrat (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G) = x := by
  unfold nativeCentralSubspaceCoordinateRecovery
  rw [native_central_subspace_lattice_coordinates_exponential (I := I) Γ V hV hrat, nativeLieGlobalLogarithm_exponential,
    finiteRealQuotientSectionRetraction_subtype]
  exact (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFun.apply_symm_apply x

theorem native_central_subspace_coordinate_recovery_right (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) (g : G) (hg : g ∈ (nativeCentralSubspaceSubgroup (I := I) V hV)) :
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat (nativeCentralSubspaceCoordinateRecovery (I := I) Γ V hV hrat g) : G) = g := by
  obtain ⟨x, hx⟩ := (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat).surjective ⟨g, hg⟩
  have he : (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G) = g := congrArg Subtype.val hx
  rw [← he, native_central_subspace_coordinate_recovery_coordinates (I := I) Γ V hV hrat]

theorem native_central_subspace_coordinate_recovery_contMDiff (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ (V)) → ℝ) ∞
      (nativeCentralSubspaceCoordinateRecovery (I := I) Γ V hV hrat) := by
  let P := finiteRealQuotientSectionRetraction (V)
  have hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ P :=
    P.contDiff.contMDiff
  exact (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFunL.contDiff.contMDiff.comp
    (hP.comp (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I)))

end Hindman168
