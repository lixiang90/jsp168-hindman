import Hindman168.NativeCenterLatticeCoordinates
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! The actual center coordinates modulo their original integer lattice. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_lattice_coordinates_add (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x y : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    nativeCenterLatticeCoordinates (I := I) Γ (x+y) =
      nativeCenterLatticeCoordinates (I := I) Γ x * nativeCenterLatticeCoordinates (I := I) Γ y := by
  change nativeLieCenterExponentialHomeomorph
    ((nativeCenterLatticeRealBasis (I := I) Γ).equivFunL.symm (x+y)) = _
  rw [map_add, nativeLieCenterExponentialHomeomorph_add]
  rfl

theorem native_center_lattice_coordinates_symm_mul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g h : Subgroup.center G) :
    (nativeCenterLatticeCoordinates (I := I) Γ).symm (g*h) =
      (nativeCenterLatticeCoordinates (I := I) Γ).symm g +
      (nativeCenterLatticeCoordinates (I := I) Γ).symm h := by
  apply (nativeCenterLatticeCoordinates (I := I) Γ).injective
  rw [native_center_lattice_coordinates_add]
  simp only [Homeomorph.apply_symm_apply]

noncomputable def nativeCenterTorusProjection (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : Subgroup.center G) :
    UnitAddTorus (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :=
  fun i => ((nativeCenterLatticeCoordinates (I := I) Γ).symm g i : UnitAddCircle)

theorem native_center_torus_projection_mul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g h : Subgroup.center G) :
    nativeCenterTorusProjection (I := I) Γ (g*h) =
      nativeCenterTorusProjection (I := I) Γ g + nativeCenterTorusProjection (I := I) Γ h := by
  funext i
  simp only [nativeCenterTorusProjection, native_center_lattice_coordinates_symm_mul,
    Pi.add_apply, AddCircle.coe_add]

theorem native_center_torus_projection_one (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeCenterTorusProjection (I := I) Γ 1 = 0 := by
  have h := native_center_torus_projection_mul (I := I) Γ 1 1
  exact (add_left_cancel (show nativeCenterTorusProjection (I := I) Γ 1 + 0 =
    nativeCenterTorusProjection (I := I) Γ 1 + nativeCenterTorusProjection (I := I) Γ 1
      by simpa only [one_mul, add_zero] using h)).symm

theorem native_center_torus_projection_inv (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : Subgroup.center G) :
    nativeCenterTorusProjection (I := I) Γ g⁻¹ = -nativeCenterTorusProjection (I := I) Γ g := by
  have h := native_center_torus_projection_mul (I := I) Γ g g⁻¹
  rw [mul_inv_cancel, native_center_torus_projection_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem native_center_torus_projection_kernel (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : Subgroup.center G) :
    nativeCenterTorusProjection (I := I) Γ g = 0 ↔ (g : G) ∈ Γ := by
  have h := native_center_lattice_coordinates_mem_iff (I := I) Γ
    ((nativeCenterLatticeCoordinates (I := I) Γ).symm g)
  rw [Homeomorph.apply_symm_apply] at h
  rw [h, funext_iff]
  simp only [nativeCenterTorusProjection, Pi.zero_apply]
  simp_rw [AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, eq_comm]

theorem native_center_torus_projection_surjective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Surjective (nativeCenterTorusProjection (I := I) Γ) := by
  intro y
  have h : ∀ i, ∃ x : ℝ, (x : UnitAddCircle) = y i :=
    fun i => QuotientAddGroup.mk_surjective (y i)
  choose x hx using h
  refine ⟨nativeCenterLatticeCoordinates (I := I) Γ x, ?_⟩
  funext i
  simpa only [nativeCenterTorusProjection, Homeomorph.symm_apply_apply] using hx i

theorem native_center_torus_projection_continuous (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Continuous (nativeCenterTorusProjection (I := I) Γ) := by
  apply continuous_pi
  intro i
  exact continuous_quotient_mk'.comp
    ((continuous_apply i).comp (nativeCenterLatticeCoordinates (I := I) Γ).symm.continuous)

end Hindman168
