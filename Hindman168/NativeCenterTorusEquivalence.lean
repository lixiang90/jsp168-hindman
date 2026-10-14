import Hindman168.NativeCenterTorusProjection
import Hindman168.NativeCenterLattice
import Mathlib.Topology.Algebra.Group.Quotient

/-! The genuine compact center modulo the original center lattice is a torus. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterTorusCosetMap (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) →
      UnitAddTorus (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :=
  Quotient.lift (nativeCenterTorusProjection (I := I) Γ) (fun g h hgh => by
    have hz := (native_center_torus_projection_kernel (I := I) Γ (g⁻¹*h)).mpr
      ((QuotientGroup.leftRel_apply (s := Γ.subgroupOf (Subgroup.center G))).mp hgh)
    rw [native_center_torus_projection_mul, native_center_torus_projection_inv] at hz
    exact neg_add_eq_zero.mp hz)

theorem native_center_torus_coset_map_mk (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : Subgroup.center G) :
    nativeCenterTorusCosetMap (I := I) Γ
      (g : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) =
        nativeCenterTorusProjection (I := I) Γ g := rfl

theorem native_center_torus_coset_map_continuous (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Continuous (nativeCenterTorusCosetMap (I := I) Γ) :=
  continuous_quot_lift _ (native_center_torus_projection_continuous (I := I) Γ)

theorem native_center_torus_coset_map_bijective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Bijective (nativeCenterTorusCosetMap (I := I) Γ) := by
  constructor
  · intro a b
    induction a, b using Quotient.inductionOn₂ with
    | _ g h =>
      intro he
      apply QuotientGroup.eq.mpr
      change ((g⁻¹*h : Subgroup.center G) : G) ∈ Γ
      apply (native_center_torus_projection_kernel (I := I) Γ (g⁻¹*h)).mp
      rw [native_center_torus_projection_mul, native_center_torus_projection_inv]
      change nativeCenterTorusProjection (I := I) Γ g = nativeCenterTorusProjection (I := I) Γ h at he
      rw [he, neg_add_cancel]
  · intro y
    obtain ⟨g, hg⟩ := native_center_torus_projection_surjective (I := I) Γ y
    exact ⟨(g : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)), hg⟩

noncomputable def nativeCenterTorusHomeomorph (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    ((Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) ≃ₜ
      UnitAddTorus (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) := by
  letI := nativeLattice_center_quotient_compactSpace (I := I) Γ
  exact (Equiv.ofBijective (nativeCenterTorusCosetMap (I := I) Γ)
    (native_center_torus_coset_map_bijective (I := I) Γ)).toHomeomorphOfContinuousClosed
      (native_center_torus_coset_map_continuous (I := I) Γ)
      (native_center_torus_coset_map_continuous (I := I) Γ).isClosedMap

theorem native_center_torus_homeomorph_mk (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : Subgroup.center G) :
    nativeCenterTorusHomeomorph (I := I) Γ
      (g : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) =
        nativeCenterTorusProjection (I := I) Γ g := rfl

theorem native_center_torus_homeomorph_mul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (z w : (Subgroup.center G) ⧸ Γ.subgroupOf (Subgroup.center G)) :
    nativeCenterTorusHomeomorph (I := I) Γ (z*w) =
      nativeCenterTorusHomeomorph (I := I) Γ z + nativeCenterTorusHomeomorph (I := I) Γ w := by
  induction z, w using Quotient.inductionOn₂ with
  | _ z w => exact native_center_torus_projection_mul (I := I) Γ z w

theorem native_center_torus_homeomorph_one (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeCenterTorusHomeomorph (I := I) Γ 1 = 0 :=
  native_center_torus_projection_one (I := I) Γ

theorem native_center_torus_homeomorph_symm_add (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (a b : UnitAddTorus (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))))) :
    (nativeCenterTorusHomeomorph (I := I) Γ).symm (a+b) =
      (nativeCenterTorusHomeomorph (I := I) Γ).symm a *
      (nativeCenterTorusHomeomorph (I := I) Γ).symm b := by
  apply (nativeCenterTorusHomeomorph (I := I) Γ).injective
  rw [native_center_torus_homeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]

theorem native_center_torus_homeomorph_symm_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (nativeCenterTorusHomeomorph (I := I) Γ).symm 0 = 1 := by
  apply (nativeCenterTorusHomeomorph (I := I) Γ).injective
  rw [Homeomorph.apply_symm_apply, native_center_torus_homeomorph_one]

end Hindman168
