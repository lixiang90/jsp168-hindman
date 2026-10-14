import Hindman168.NativeFilteredHorizontalLatticeImage
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.Group.Quotient

/-! The actual horizontal torus factor of the original group and lattice.
No normality of the original lattice is required for the coset map. -/

namespace Hindman168
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeHorizontalTorusProjection (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := I) Γ) :=
  fun i => (nativeFilteredHorizontalCoordinates (I := I) Γ g i : UnitAddCircle)

theorem native_horizontal_torus_projection_mul (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g h : G) :
    nativeHorizontalTorusProjection (I := I) Γ (g*h) =
      nativeHorizontalTorusProjection (I := I) Γ g + nativeHorizontalTorusProjection (I := I) Γ h := by
  funext i
  simp only [nativeHorizontalTorusProjection, native_filtered_horizontal_coordinates_mul,
    Pi.add_apply, AddCircle.coe_add]

theorem native_horizontal_torus_projection_one (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    nativeHorizontalTorusProjection (I := I) Γ 1 = 0 := by
  have h := native_horizontal_torus_projection_mul (I := I) Γ 1 1
  exact (add_left_cancel (show nativeHorizontalTorusProjection (I := I) Γ 1 + 0 =
    nativeHorizontalTorusProjection (I := I) Γ 1 + nativeHorizontalTorusProjection (I := I) Γ 1
      by simpa only [one_mul, add_zero] using h)).symm

theorem native_horizontal_torus_projection_inv (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    nativeHorizontalTorusProjection (I := I) Γ g⁻¹ = -nativeHorizontalTorusProjection (I := I) Γ g := by
  have h := native_horizontal_torus_projection_mul (I := I) Γ g g⁻¹
  rw [mul_inv_cancel, native_horizontal_torus_projection_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem native_horizontal_torus_projection_zero_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    nativeHorizontalTorusProjection (I := I) Γ g = 0 ↔
      ∀ i, ∃ n : ℤ, nativeFilteredHorizontalCoordinates (I := I) Γ g i = (n : ℝ) := by
  rw [funext_iff]
  simp only [nativeHorizontalTorusProjection, Pi.zero_apply]
  simp_rw [AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, eq_comm]

theorem native_horizontal_torus_projection_lattice_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] {g : G} (hg : g ∈ Γ) :
    nativeHorizontalTorusProjection (I := I) Γ g = 0 := by
  apply (native_horizontal_torus_projection_zero_iff (I := I) Γ g).mpr
  exact (native_filtered_horizontal_lattice_image_mem_iff (I := I) Γ _).mp ⟨g, hg, rfl⟩

theorem native_horizontal_torus_projection_surjective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Surjective (nativeHorizontalTorusProjection (I := I) Γ) := by
  intro y
  have h : ∀ i, ∃ x : ℝ, (x : UnitAddCircle) = y i :=
    fun i => QuotientAddGroup.mk_surjective (y i)
  choose x hx using h
  obtain ⟨g, hg⟩ := native_filtered_horizontal_coordinates_surjective (I := I) Γ x
  refine ⟨g, ?_⟩
  funext i
  change (nativeFilteredHorizontalCoordinates (I := I) Γ g i : UnitAddCircle) = y i
  rw [hg]
  exact hx i

theorem native_horizontal_torus_projection_continuous (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Continuous (nativeHorizontalTorusProjection (I := I) Γ) := by
  apply continuous_pi
  intro i
  exact continuous_quotient_mk'.comp
    ((continuous_apply i).comp (native_filtered_horizontal_coordinates_continuous (I := I) Γ))

noncomputable def nativeHorizontalTorusCosetMap (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    G ⧸ Γ → UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := I) Γ) :=
  Quotient.lift (nativeHorizontalTorusProjection (I := I) Γ) (fun g h hgh => by
    have hz := native_horizontal_torus_projection_lattice_zero (I := I) Γ
      (QuotientGroup.leftRel_apply.mp hgh)
    rw [native_horizontal_torus_projection_mul, native_horizontal_torus_projection_inv] at hz
    exact neg_add_eq_zero.mp hz)

theorem native_horizontal_torus_coset_map_mk (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (g : G) :
    nativeHorizontalTorusCosetMap (I := I) Γ (g : G ⧸ Γ) =
      nativeHorizontalTorusProjection (I := I) Γ g := rfl

theorem native_horizontal_torus_coset_map_continuous (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Continuous (nativeHorizontalTorusCosetMap (I := I) Γ) :=
  continuous_quot_lift _ (native_horizontal_torus_projection_continuous (I := I) Γ)

theorem native_horizontal_torus_coset_map_surjective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Surjective (nativeHorizontalTorusCosetMap (I := I) Γ) := by
  intro y
  obtain ⟨g, hg⟩ := native_horizontal_torus_projection_surjective (I := I) Γ y
  exact ⟨(g : G ⧸ Γ), hg⟩

end Hindman168
