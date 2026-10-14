import Hindman168.NativeCenterLatticeCoordinates
import Hindman168.NativeCenterQuotientNormedModel
import Hindman168.ProjectionAppendIndependent

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_lattice_columns_linear_independent (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    LinearIndependent ℝ (fun i => (nativeCenterLatticeRealBasis (I := I) Γ i).val) := by
  exact (nativeCenterLatticeRealBasis (I := I) Γ).linearIndependent.map'
    (nativeLieCenterModel (I := I) (G := G)).subtype (Submodule.ker_subtype _)

theorem native_center_lattice_columns_projection_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    nativeCenterQuotientProjection (I := I) (G := G)
      (nativeCenterLatticeRealBasis (I := I) Γ i).val = 0 := by
  change (Submodule.Quotient.mk (nativeCenterLatticeRealBasis (I := I) Γ i).val :
    E ⧸ nativeLieCenterModel (I := I) (G := G)) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (nativeCenterLatticeRealBasis (I := I) Γ i).property

theorem native_center_lattice_lift_append_independent {m : ℕ} (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : Fin m → E ⧸ nativeLieCenterModel (I := I) (G := G)) (hv : LinearIndependent ℝ v)
    (u : Fin m → E)
    (hu : ∀ i, nativeCenterQuotientProjection (I := I) (G := G) (u i) = v i) :
    LinearIndependent ℝ (Fin.append u (fun i => (nativeCenterLatticeRealBasis (I := I) Γ i).val)) := by
  apply projection_append_linear_independent
    (nativeCenterQuotientProjection (I := I) (G := G)).toLinearMap
  · have he : (fun i => nativeCenterQuotientProjection (I := I) (G := G) (u i)) = v := funext hu
    change LinearIndependent ℝ (fun i => nativeCenterQuotientProjection (I := I) (G := G) (u i))
    rw [he]
    exact hv
  · exact native_center_lattice_columns_linear_independent Γ
  · exact native_center_lattice_columns_projection_zero Γ

end Hindman168
