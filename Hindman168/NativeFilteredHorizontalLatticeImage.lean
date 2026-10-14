import Hindman168.NativeFilteredHorizontalCoordinates

namespace Hindman168
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_filtered_horizontal_coordinates_surjective (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Function.Surjective (nativeFilteredHorizontalCoordinates (I := I) Γ) := by
  intro y
  let x : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    if hi : i ∈ nativeFilteredHorizontalIndices (I := I) Γ then y ⟨i, hi⟩ else 0
  refine ⟨nativeLatticeFilteredDiffeomorph (I := I) Γ x, ?_⟩
  rw [native_filtered_horizontal_coordinates_diffeomorph (I := I) Γ]
  funext i
  exact dif_pos i.property

theorem native_filtered_horizontal_lattice_image_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (y : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℝ) :
    y ∈ nativeFilteredHorizontalCoordinates (I := I) Γ '' (Γ : Set G) ↔
      ∀ i, ∃ n : ℤ, y i = (n : ℝ) := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩ i
    let x := (nativeLatticeFilteredDiffeomorph (I := I) Γ).symm γ
    have hx : ∀ j, ∃ n : ℤ, x j = (n : ℝ) :=
      (native_lattice_filtered_diffeomorph_mem_iff (I := I) Γ x).mp
        (by
          change nativeLatticeFilteredDiffeomorph (I := I) Γ
            ((nativeLatticeFilteredDiffeomorph (I := I) Γ).symm γ) ∈ Γ
          rw [Diffeomorph.apply_symm_apply]
          exact hγ)
    obtain ⟨n, hn⟩ := hx i.val
    have he := congrFun (native_filtered_horizontal_coordinates_diffeomorph (I := I) Γ x) i
    rw [show nativeLatticeFilteredDiffeomorph (I := I) Γ x = γ from
      (nativeLatticeFilteredDiffeomorph (I := I) Γ).apply_symm_apply γ] at he
    exact ⟨n, he.trans hn⟩
  · intro hy
    let x : Fin (Module.finrank ℝ E) → ℝ := fun i =>
      if hi : i ∈ nativeFilteredHorizontalIndices (I := I) Γ then y ⟨i, hi⟩ else 0
    have hx : ∀ j, ∃ n : ℤ, x j = (n : ℝ) := by
      intro j
      by_cases hj : j ∈ nativeFilteredHorizontalIndices (I := I) Γ
      · simpa only [x, dif_pos hj] using hy ⟨j, hj⟩
      · exact ⟨0, by simp only [x, dif_neg hj, Int.cast_zero]⟩
    refine ⟨nativeLatticeFilteredDiffeomorph (I := I) Γ x,
      (native_lattice_filtered_diffeomorph_mem_iff (I := I) Γ x).mpr hx, ?_⟩
    rw [native_filtered_horizontal_coordinates_diffeomorph (I := I) Γ]
    funext i
    exact dif_pos i.property

end Hindman168
