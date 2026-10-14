import Hindman168.NativeCentralSubspaceLatticeCoordinates

namespace Hindman168
open Module Submodule Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceLatticeIntegerBasis (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    Basis (Fin (Module.finrank ℝ V)) ℤ (nativeCentralSubspaceLogLattice (I := I) Γ V hV) := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  letI := nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat
  exact integerLatticeIntegerBasis (nativeCentralSubspaceLogLattice (I := I) Γ V hV)

theorem native_central_subspace_lattice_integer_real_columns (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (i : Fin (Module.finrank ℝ V)) :
    (nativeCentralSubspaceLatticeIntegerBasis (I := I) Γ V hV hrat i).val =
      nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  letI := nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat
  change (integerLatticeIntegerBasis (nativeCentralSubspaceLogLattice (I := I) Γ V hV) i : V) =
    integerLatticeRealBasis (nativeCentralSubspaceLogLattice (I := I) Γ V hV) i
  rw [integerLatticeRealBasis, Basis.ofZLatticeBasis_apply]
  rfl

theorem native_central_subspace_lattice_columns_real_span (Γ : Subgroup G) [DiscreteTopology Γ]
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    span ℝ (range (fun i => (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val)) = V := by
  have h := congrArg (fun P : Submodule ℝ V => P.map V.subtype)
    (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
  simpa only [← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using h

end Hindman168
