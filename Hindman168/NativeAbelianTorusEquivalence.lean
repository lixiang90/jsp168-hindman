import Hindman168.NativeHorizontalTorusProjection

/-! Actual abelian cosets are the standard horizontal torus, using the
original filtered lattice coordinates and the original step bound. -/

namespace Hindman168
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_abelian_filtered_layer_start_one (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) :
    nativeLatticeFilteredLayerStart (I := I) Γ 1 = Module.finrank ℝ E := by
  apply le_antisymm (native_lattice_filtered_layer_start_spec (I := I) Γ 1).1
  rw [← native_lattice_filtered_layer_start_nilpotencyClass (I := I) Γ]
  exact native_lattice_filtered_layer_start_monotone (I := I) Γ hstep

theorem native_abelian_horizontal_indices_univ (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) :
    nativeFilteredHorizontalIndices (I := I) Γ = Finset.univ := by
  ext i
  rw [native_filtered_horizontal_indices_mem_iff (I := I) Γ,
    native_abelian_filtered_layer_start_one (I := I) Γ hstep]
  simp only [Finset.mem_univ, iff_true]
  exact i.isLt

theorem native_abelian_horizontal_torus_kernel (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) (g : G) :
    nativeHorizontalTorusProjection (I := I) Γ g = 0 ↔ g ∈ Γ := by
  constructor
  · intro hg
    let x := (nativeLatticeFilteredDiffeomorph (I := I) Γ).symm g
    have hx : nativeLatticeFilteredDiffeomorph (I := I) Γ x = g :=
      (nativeLatticeFilteredDiffeomorph (I := I) Γ).apply_symm_apply g
    have hi := (native_horizontal_torus_projection_zero_iff (I := I) Γ g).mp hg
    have hint : ∀ j, ∃ n : ℤ, x j = (n : ℝ) := by
      intro j
      have hj : j ∈ nativeFilteredHorizontalIndices (I := I) Γ := by
        rw [native_abelian_horizontal_indices_univ (I := I) Γ hstep]
        exact Finset.mem_univ j
      have he := congrFun (native_filtered_horizontal_coordinates_diffeomorph (I := I) Γ x)
        (⟨j, hj⟩ : ↥(nativeFilteredHorizontalIndices (I := I) Γ))
      rw [hx] at he
      exact he ▸ hi ⟨j, hj⟩
    exact hx ▸ (native_lattice_filtered_diffeomorph_mem_iff (I := I) Γ x).mpr hint
  · exact native_horizontal_torus_projection_lattice_zero (I := I) Γ

theorem native_abelian_horizontal_torus_coset_injective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) :
    Function.Injective (nativeHorizontalTorusCosetMap (I := I) Γ) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | _ g h =>
    intro he
    apply QuotientGroup.eq.mpr
    apply (native_abelian_horizontal_torus_kernel (I := I) Γ hstep (g⁻¹*h)).mp
    rw [native_horizontal_torus_projection_mul, native_horizontal_torus_projection_inv]
    change nativeHorizontalTorusProjection (I := I) Γ g =
      nativeHorizontalTorusProjection (I := I) Γ h at he
    rw [he, neg_add_cancel]

noncomputable def nativeAbelianTorusHomeomorph (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) :
    (G ⧸ Γ) ≃ₜ UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := I) Γ) :=
  (Equiv.ofBijective (nativeHorizontalTorusCosetMap (I := I) Γ)
    ⟨native_abelian_horizontal_torus_coset_injective (I := I) Γ hstep,
      native_horizontal_torus_coset_map_surjective (I := I) Γ⟩).toHomeomorphOfContinuousClosed
    (native_horizontal_torus_coset_map_continuous (I := I) Γ)
    (native_horizontal_torus_coset_map_continuous (I := I) Γ).isClosedMap

theorem native_abelian_torus_homeomorph_mk (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (hstep : Group.nilpotencyClass G ≤ 1) (g : G) :
    nativeAbelianTorusHomeomorph (I := I) Γ hstep (g : G ⧸ Γ) =
      nativeHorizontalTorusProjection (I := I) Γ g := rfl

end Hindman168
