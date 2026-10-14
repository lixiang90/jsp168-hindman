import Hindman168.IntegerLatticeCoordinates
import Hindman168.NativeCenterRationalBasis

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterLatticeRealBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) ℝ
      (nativeLieCenterModel (I := I) (G := G)) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integerLatticeRealBasis (nativeCenterLogLattice (I := I) Γ)

theorem native_center_lattice_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    nativeLieExponential (I := I) (G := G)
      (nativeCenterLatticeRealBasis (I := I) Γ i).val ∈ Γ := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integer_lattice_real_basis_column_mem (nativeCenterLogLattice (I := I) Γ) i

theorem native_center_lattice_exponential_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : nativeLieCenterModel (I := I) (G := G)) :
    nativeLieExponential (I := I) (G := G) v.val ∈ Γ ↔
      ∀ i, ∃ n : ℤ, (nativeCenterLatticeRealBasis (I := I) Γ).repr v i = (n : ℝ) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integer_lattice_mem_iff_integral_coordinates (nativeCenterLogLattice (I := I) Γ) v

noncomputable def nativeCenterLatticeCoordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) ≃ₜ
      Subgroup.center G :=
  (nativeCenterLatticeRealBasis (I := I) Γ).equivFunL.symm.toHomeomorph.trans
    (nativeLieCenterExponentialHomeomorph (I := I) (G := G))

theorem native_center_lattice_coordinates_exponential (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLatticeCoordinates (I := I) Γ x : G) =
      nativeLieExponential (I := I) (G := G)
        ((nativeCenterLatticeRealBasis (I := I) Γ).equivFun.symm x).val := rfl

theorem native_center_lattice_coordinates_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLatticeCoordinates (I := I) Γ x : G) ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  rw [native_center_lattice_coordinates_exponential,
    native_center_lattice_exponential_mem_iff_coordinates]
  have he := (nativeCenterLatticeRealBasis (I := I) Γ).equivFun.apply_symm_apply x
  change (∀ i, ∃ n : ℤ, ((nativeCenterLatticeRealBasis (I := I) Γ).equivFun
    ((nativeCenterLatticeRealBasis (I := I) Γ).equivFun.symm x)) i = (n : ℝ)) ↔ _
  rw [he]

end Hindman168
