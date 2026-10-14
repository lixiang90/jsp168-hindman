import Hindman168.NativeCentralSubspaceLatticeCoordinates
import Hindman168.NativeCentralSubspaceQuotientCharted
import Hindman168.ProjectionAppendIndependent

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem native_central_subspace_lattice_columns_linear_independent (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    LinearIndependent ℝ (fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val) := by
  exact (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).linearIndependent.map'
    (V).subtype (Submodule.ker_subtype _)

theorem native_central_subspace_lattice_columns_projection_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (i : Fin (Module.finrank ℝ (V))) :
    finiteRealQuotientProjection V
      (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val = 0 := by
  change (Submodule.Quotient.mk (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val :
    E ⧸ V) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).property

theorem native_central_subspace_lattice_lift_append_independent {m : ℕ} (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (v : Fin m → E ⧸ V) (hv : LinearIndependent ℝ v)
    (u : Fin m → E)
    (hu : ∀ i, finiteRealQuotientProjection V (u i) = v i) :
    LinearIndependent ℝ (Fin.append u (fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val)) := by
  apply projection_append_linear_independent
    (finiteRealQuotientProjection V).toLinearMap
  · have he : (fun i => finiteRealQuotientProjection V (u i)) = v := funext hu
    change LinearIndependent ℝ (fun i => finiteRealQuotientProjection V (u i))
    rw [he]
    exact hv
  · exact native_central_subspace_lattice_columns_linear_independent (I := I) Γ V hV hrat
  · exact native_central_subspace_lattice_columns_projection_zero (I := I) Γ V hV hrat

end Hindman168
