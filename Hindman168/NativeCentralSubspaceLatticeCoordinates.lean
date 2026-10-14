import Hindman168.IntegerLatticeCoordinates
import Hindman168.NativeCentralSubspaceLogSpanning
import Hindman168.NativeCentralSubspaceExponentialHomeomorph

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceLatticeRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    Basis (Fin (Module.finrank ℝ (V))) ℝ
      (V) := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  letI := nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat
  exact integerLatticeRealBasis (nativeCentralSubspaceLogLattice (I := I) Γ V hV)

theorem native_central_subspace_lattice_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (i : Fin (Module.finrank ℝ (V))) :
    nativeLieExponential (I := I) (G := G)
      (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val ∈ Γ := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  letI := nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat
  exact integer_lattice_real_basis_column_mem (nativeCentralSubspaceLogLattice (I := I) Γ V hV) i

theorem native_central_subspace_lattice_exponential_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (v : V) :
    nativeLieExponential (I := I) (G := G) v.val ∈ Γ ↔
      ∀ i, ∃ n : ℤ, (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).repr v i = (n : ℝ) := by
  letI := nativeCentralSubspaceLogLattice_discrete (I := I) Γ V hV
  letI := nativeCentralSubspaceLogLattice_isZLattice (I := I) Γ V hV hrat
  exact integer_lattice_mem_iff_integral_coordinates (nativeCentralSubspaceLogLattice (I := I) Γ V hV) v

noncomputable def nativeCentralSubspaceLatticeCoordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V) :
    (Fin (Module.finrank ℝ (V)) → ℝ) ≃ₜ
      nativeCentralSubspaceSubgroup (I := I) V hV :=
  (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFunL.symm.toHomeomorph.trans
    (nativeCentralSubspaceExponentialHomeomorph (I := I) V hV)

theorem native_central_subspace_lattice_coordinates_exponential (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (x : Fin (Module.finrank ℝ (V)) → ℝ) :
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G) =
      nativeLieExponential (I := I) (G := G)
        ((nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFun.symm x).val := rfl

theorem native_central_subspace_lattice_coordinates_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (x : Fin (Module.finrank ℝ (V)) → ℝ) :
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G) ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  rw [native_central_subspace_lattice_coordinates_exponential (I := I) Γ V hV hrat,
    native_central_subspace_lattice_exponential_mem_iff_coordinates (I := I) Γ V hV hrat]
  have he := (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFun.apply_symm_apply x
  change (∀ i, ∃ n : ℤ, ((nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFun
    ((nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat).equivFun.symm x)) i = (n : ℝ)) ↔ _
  rw [he]

end Hindman168
