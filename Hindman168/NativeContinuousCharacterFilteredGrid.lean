import Hindman168.NativeContinuousHorizontalCharacter
import Hindman168.NativeFilteredHorizontalGrid

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeFilteredContinuousCharacterSize (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : ↥(nativeFilteredHorizontalIndices (I := I) Γ) =>
    χ (nativeLieExponential (I := I) (G := G)
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val))) :
    EuclideanSpace ℝ ↥(nativeFilteredHorizontalIndices (I := I) Γ))‖

theorem native_filtered_continuous_character_size_eq (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) (f : E →ₗ[ℝ] ℝ)
    (hrep : ∀ g, χ g = f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)) :
    nativeFilteredContinuousCharacterSize (I := I) Γ χ =
      nativeFilteredHorizontalCoefficientSize (I := I) Γ f := by
  have he : (fun i : ↥(nativeFilteredHorizontalIndices (I := I) Γ) =>
      χ (nativeLieExponential (I := I) (G := G)
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val))) =
      fun i => f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val) := by
    funext i
    rw [hrep, nativeLieGlobalLogarithm_exponential]
  unfold nativeFilteredContinuousCharacterSize nativeFilteredHorizontalCoefficientSize
  rw [he]

theorem native_filtered_continuous_character_grid_contains (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) (hcont : Continuous χ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (hne : χ ≠ 0)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ, χ γ = (m : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hsize : nativeFilteredContinuousCharacterSize (I := I) Γ χ ≤ M) :
    ∃ f ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈M⌉₊,
      ∀ g, χ g = f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := by
  obtain ⟨f, ⟨hf, hrep⟩, _⟩ :=
    native_continuous_horizontal_character_representation (I := I) Γ χ hcont hmul hne hint
  have hs : nativeFilteredHorizontalCoefficientSize (I := I) Γ f.toLinearMap ≤ M := by
    rw [← native_filtered_continuous_character_size_eq (I := I) Γ χ f.toLinearMap hrep]
    exact hsize
  exact ⟨f.toLinearMap, native_filtered_horizontal_size_grid_contains (I := I) Γ M hM _ hf hs, hrep⟩

theorem native_filtered_continuous_character_bounded_normalization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : G → ℝ) (hcont : Continuous χ)
    (hmul : ∀ g h, χ (g*h) = χ g + χ h) (hne : χ ≠ 0)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ, χ γ = (m : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hsize : nativeFilteredContinuousCharacterSize (I := I) Γ χ ≤ M) :
    ∃ (V : E) (K : ℕ), V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
      χ (nativeLieExponential (I := I) (G := G) V) = 1 ∧ 0 < K ∧ K ≤ ⌈M⌉₊ ∧
      nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
  obtain ⟨f, ⟨hf, hrep⟩, _⟩ :=
    native_continuous_horizontal_character_representation (I := I) Γ χ hcont hmul hne hint
  have hs : nativeFilteredHorizontalCoefficientSize (I := I) Γ f.toLinearMap ≤ M := by
    rw [← native_filtered_continuous_character_size_eq (I := I) Γ χ f.toLinearMap hrep]
    exact hsize
  obtain ⟨V, K, hV, hval, hK, hbound, hΓ⟩ :=
    native_filtered_horizontal_size_bounded_normalization (I := I) Γ M hM _ hf hs
  refine ⟨V, K, hV, ?_, hK, hbound, hΓ⟩
  rw [hrep, nativeLieGlobalLogarithm_exponential]
  exact hval

end Hindman168
