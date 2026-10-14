import Hindman168.NativeFilteredHorizontalSize
import Hindman168.NativeFilteredSmoothIntegerCharacterNormalization

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_filtered_horizontal_size_grid_contains (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M) (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f)
    (hsize : nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M) :
    f ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈M⌉₊ := by
  obtain ⟨a, ⟨ha, hne, htail⟩, _⟩ := native_filtered_horizontal_integer_representation (I := I) Γ f hf
  have hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a).ker := ha.symm ▸ hf.2.1
  have hs : roughHorizontalIntegerSize Finset.univ a ≤ M := by
    rw [native_filtered_horizontal_full_integer_size_eq (I := I) Γ a htail,
      ← native_filtered_integer_horizontal_size (I := I) Γ a, ha]
    exact hsize
  rw [← ha]
  exact native_filtered_smooth_basis_integer_grid_size_contains (I := I) Γ M hM a hne hcomm hs

theorem native_filtered_horizontal_size_bounded_normalization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M) (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f)
    (hsize : nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M) :
    ∃ (V : E) (K : ℕ), V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
      f V = 1 ∧ 0 < K ∧ K ≤ ⌈M⌉₊ ∧
      nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ :=
  native_filtered_smooth_integer_grid_bounded_normalization (I := I) Γ ⌈M⌉₊
    (native_filtered_horizontal_size_grid_contains (I := I) Γ M hM f hf hsize)

theorem native_filtered_horizontal_size_no_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f) :
    0 < nativeFilteredHorizontalCoefficientSize (I := I) Γ f := by
  have hn := native_filtered_horizontal_coefficient_size_nonnegative (I := I) Γ f
  by_contra h
  have hz : nativeFilteredHorizontalCoefficientSize (I := I) Γ f = 0 := le_antisymm (le_of_not_gt h) hn
  obtain ⟨V, K, _, _, hK, hbound, _⟩ :=
    native_filtered_horizontal_size_bounded_normalization (I := I) Γ 0 le_rfl f hf (le_of_eq hz)
  have hK0 : K ≤ 0 := by simpa only [Nat.ceil_zero] using hbound
  omega

end Hindman168
