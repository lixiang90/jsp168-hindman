import Hindman168.NativeCentralSubspaceTorusProjection
import Hindman168.NativeCentralSubspaceLieIdeal
import Hindman168.NativeRationalLatticeCompact
import Hindman168.CentralSubgroupCosetAction

/-! ACTUAL rational central subspace modulo its ORIGINAL restricted
lattice is the ACTUAL finite torus, with genuine compactness and group laws. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

variable (Γ : Subgroup G) [DiscreteTopology Γ] (V : Submodule ℝ E)
  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
  (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
local notation "N" => nativeCentralSubspaceSubgroup (I := I) V hV

noncomputable def nativeCentralSubspaceTorusCosetMap :
    (N ⧸ Γ.comap (N).subtype) → UnitAddTorus (Fin (Module.finrank ℝ V)) :=
  Quotient.lift (nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat) (fun g h hgh => by
    have hz := (native_central_subspace_torus_projection_kernel (I := I) Γ V hV hrat (g⁻¹*h)).mpr
      ((QuotientGroup.leftRel_apply (s := Γ.comap (N).subtype)).mp hgh)
    rw [native_central_subspace_torus_projection_mul,native_central_subspace_torus_projection_inv] at hz
    exact neg_add_eq_zero.mp hz)

theorem native_central_subspace_torus_coset_map_mk (g : N) :
    nativeCentralSubspaceTorusCosetMap (I := I) Γ V hV hrat (g : N ⧸ Γ.comap (N).subtype) =
      nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g := rfl

theorem native_central_subspace_torus_coset_map_continuous :
    Continuous (nativeCentralSubspaceTorusCosetMap (I := I) Γ V hV hrat) :=
  continuous_quot_lift _ (native_central_subspace_torus_projection_continuous (I := I) Γ V hV hrat)

theorem native_central_subspace_torus_coset_map_bijective :
    Function.Bijective (nativeCentralSubspaceTorusCosetMap (I := I) Γ V hV hrat) := by
  constructor
  · intro a b
    induction a,b using Quotient.inductionOn₂ with
    | _ g h =>
      intro he
      apply QuotientGroup.eq.mpr
      change ((g⁻¹*h : N) : G) ∈ Γ
      apply (native_central_subspace_torus_projection_kernel (I := I) Γ V hV hrat (g⁻¹*h)).mp
      rw [native_central_subspace_torus_projection_mul,native_central_subspace_torus_projection_inv]
      change nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g =
        nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat h at he
      rw [he,neg_add_cancel]
  · intro y
    obtain ⟨g,hg⟩ := native_central_subspace_torus_projection_surjective (I := I) Γ V hV hrat y
    exact ⟨(g : N ⧸ Γ.comap (N).subtype),hg⟩

include hrat in
theorem native_central_subspace_lattice_quotient_compact [CompactSpace (G ⧸ Γ)] :
    CompactSpace (N ⧸ Γ.comap (N).subtype) := by
  have h := nativeRationalLieLattice_quotient_compact (I := I) Γ
    (nativeCentralSubspaceLieIdeal (I := I) V hV).toLieSubalgebra hrat
  rw [nativeCentralSubspaceLieIdeal_subgroup] at h
  exact h

noncomputable def nativeCentralSubspaceTorusHomeomorph [CompactSpace (G ⧸ Γ)] :
    (N ⧸ Γ.comap (N).subtype) ≃ₜ UnitAddTorus (Fin (Module.finrank ℝ V)) := by
  letI := native_central_subspace_lattice_quotient_compact (I := I) Γ V hV hrat
  exact (Equiv.ofBijective (nativeCentralSubspaceTorusCosetMap (I := I) Γ V hV hrat)
    (native_central_subspace_torus_coset_map_bijective (I := I) Γ V hV hrat)).toHomeomorphOfContinuousClosed
      (native_central_subspace_torus_coset_map_continuous (I := I) Γ V hV hrat)
      (native_central_subspace_torus_coset_map_continuous (I := I) Γ V hV hrat).isClosedMap

variable [CompactSpace (G ⧸ Γ)]

theorem native_central_subspace_torus_homeomorph_mk (g : N) :
    nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat (g : N ⧸ Γ.comap (N).subtype) =
      nativeCentralSubspaceTorusProjection (I := I) Γ V hV hrat g := rfl

theorem native_central_subspace_torus_homeomorph_mul (z w : N ⧸ Γ.comap (N).subtype) :
    letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
    nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat (z*w) =
      nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat z +
        nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat w := by
  letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  induction z,w using Quotient.inductionOn₂ with
  | _ z w => exact native_central_subspace_torus_projection_mul (I := I) Γ V hV hrat z w

theorem native_central_subspace_torus_homeomorph_one :
    letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
    nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat (1 : N ⧸ Γ.comap (N).subtype) = 0 := by
  letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  exact native_central_subspace_torus_projection_one (I := I) Γ V hV hrat

theorem native_central_subspace_torus_homeomorph_symm_add
    (a b : UnitAddTorus (Fin (Module.finrank ℝ V))) :
    letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
    (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).symm (a+b) =
      (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).symm a *
        (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).symm b := by
  letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  apply (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).injective
  rw [native_central_subspace_torus_homeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]

theorem native_central_subspace_torus_homeomorph_symm_zero :
    letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
    (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).symm 0 = (1 : N ⧸ Γ.comap (N).subtype) := by
  letI := central_subgroup_lattice_normal N Γ (nativeCentralSubspaceSubgroup_le_center V hV)
  apply (nativeCentralSubspaceTorusHomeomorph (I := I) Γ V hV hrat).injective
  rw [Homeomorph.apply_symm_apply,native_central_subspace_torus_homeomorph_one]

end Hindman168
