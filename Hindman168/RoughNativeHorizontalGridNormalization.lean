import Hindman168.RoughNativeHorizontalCharacterGrid
import Hindman168.RoughNativeCharacterNormalization

namespace Hindman168
open Module
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_horizontal_grid_normalization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) {χ : E →ₗ[ℝ] ℝ}
    (hχ : χ ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A) :
    ∃ V : E, V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧ χ V = 1 ∧
      ∃ K : ℕ, 0 < K ∧ nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
  have hh := ((rough_native_horizontal_grid_mem_iff Γ A χ).mp hχ).2
  let b := nativeLatticeRealBasis (E := E) (I := I) Γ
  have hnonzero : ∃ i, χ (b i) ≠ 0 := by
    by_contra! hz
    apply hh.1
    apply b.ext
    intro i
    simpa only [LinearMap.zero_apply] using hz i
  obtain ⟨i, hi⟩ := hnonzero
  have hv : b i ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    nativeLatticeRealBasis_mem_rationalLogSpan (E := E) (I := I) Γ i
  obtain ⟨r, hr⟩ := rough_native_integral_character_rational_on_span Γ χ hh.2.2 _ hv
  have hr0 : r ≠ 0 := by
    intro hz
    apply hi
    rw [hr, hz, Rat.cast_zero]
  let V : E := r⁻¹ • b i
  have hV : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).smul_mem _ hv
  have hχV : χ V = 1 := by
    dsimp [V]
    rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, hr, Rat.cast_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hr0)
  obtain ⟨K, hK, hΓ⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (E := E) (I := I) Γ V).mp hV
  refine ⟨V, hV, hχV, K, hK, ?_⟩
  rw [nativeLieExponential_nat_smul]
  exact hΓ

theorem rough_native_horizontal_grid_fixed_normalizations (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) :
    ∃ (V : ↥(roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A) → E)
      (K : ↥(roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A) → ℕ),
      ∀ χ, V χ ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        χ.val (V χ) = 1 ∧ 0 < K χ ∧
        nativeLieExponential (I := I) (G := G) ((K χ : ℝ) • V χ) ∈ Γ := by
  have hdata : ∀ χ : ↥(roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A),
      ∃ (V : E) (K : ℕ), V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        χ.val V = 1 ∧ 0 < K ∧ nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
    intro χ
    obtain ⟨V, hV, hv, K, hk, hΓ⟩ := rough_native_horizontal_grid_normalization Γ A χ.property
    exact ⟨V, K, hV, hv, hk, hΓ⟩
  choose V K hV hv hk hΓ using hdata
  exact ⟨V, K, fun χ => ⟨hV χ, hv χ, hk χ, hΓ χ⟩⟩

end Hindman168
