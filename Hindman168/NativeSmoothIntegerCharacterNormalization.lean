import Hindman168.NativeSmoothBasisIntegerCharacterGrid

/-! Normalized rational directions with explicit bounded original lattice
periods, obtained from a nonzero integer coefficient in the same smooth
original lattice basis. All choices can be fixed over the finite grid. -/

namespace Hindman168
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_smooth_integer_character_column_normalization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (a : Fin (Module.finrank ℝ E) → ℤ) (i : Fin (Module.finrank ℝ E))
    (hi : a i ≠ 0) :
    ∃ V : E, V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
      nativeSmoothBasisIntegerFunctional (I := I) Γ a V = 1 ∧
      nativeLieExponential (I := I) (G := G) (((a i).natAbs : ℝ) • V) ∈ Γ := by
  let n := a i
  let b := nativeLatticeOrderedSmoothRealBasis (I := I) Γ i
  let V : E := (n : ℚ)⁻¹ • b
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hi
  have hV : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).smul_mem _
      (native_lattice_ordered_smooth_basis_mem_rational_span (I := I) Γ i)
  refine ⟨V, hV, ?_, ?_⟩
  · dsimp only [V]
    rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, Rat.cast_inv, Rat.cast_intCast,
      native_smooth_basis_integer_functional_basis, smul_eq_mul]
    exact inv_mul_cancel₀ hn
  · have hK : ((a i).natAbs : ℝ) = |(n : ℝ)| := by
      simp only [n, Nat.cast_natAbs, Int.cast_abs]
    have hs : ((a i).natAbs : ℝ) • V = (|(n : ℝ)| * (n : ℝ)⁻¹) • b := by
      dsimp only [V]
      rw [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_inv, Rat.cast_intCast, smul_smul, hK]
    rw [hs]
    by_cases hp : 0 ≤ (n : ℝ)
    · rw [abs_of_nonneg hp, mul_inv_cancel₀ hn, one_smul]
      exact native_lattice_ordered_smooth_basis_exponential_mem (I := I) Γ i
    · rw [abs_of_neg (lt_of_not_ge hp), neg_mul, mul_inv_cancel₀ hn, neg_one_smul]
      have he : nativeLieExponential (I := I) (G := G) (-b) =
          (nativeLieExponential (I := I) (G := G) b)⁻¹ :=
        nativeLieExponential_neg (I := I) (G := G) b
      rw [he]
      exact Γ.inv_mem (native_lattice_ordered_smooth_basis_exponential_mem (I := I) Γ i)

theorem native_smooth_integer_grid_bounded_normalization (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) {f : E →ₗ[ℝ] ℝ}
    (hf : f ∈ nativeSmoothBasisIntegerCharacterGrid (I := I) Γ B) :
    ∃ (V : E) (K : ℕ), V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
      f V = 1 ∧ 0 < K ∧ K ≤ B ∧
      nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
  obtain ⟨hhor, a, hab, ha⟩ := (native_smooth_basis_integer_grid_mem_iff (I := I) Γ B f).mp hf
  have hne : a ≠ 0 := by
    intro hz
    apply hhor.1
    rw [← ha, hz, native_smooth_basis_integer_functional_zero (I := I)]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hi0 : a i ≠ 0 := hi
  obtain ⟨V, hV, hv, hΓ⟩ := native_smooth_integer_character_column_normalization (I := I) Γ a i hi0
  refine ⟨V, (a i).natAbs, hV, ?_, Int.natAbs_pos.mpr hi0, ?_, hΓ⟩
  · rw [← ha]
    exact hv
  · have habs : |a i| ≤ (B : ℤ) := abs_le.mpr (hab i)
    have hnabs : ((a i).natAbs : ℤ) ≤ (B : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hnabs

theorem native_smooth_integer_grid_fixed_bounded_normalizations (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) :
    ∃ (V : ↥(nativeSmoothBasisIntegerCharacterGrid (I := I) Γ B) → E)
      (K : ↥(nativeSmoothBasisIntegerCharacterGrid (I := I) Γ B) → ℕ),
      ∀ f, V f ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        f.val (V f) = 1 ∧ 0 < K f ∧ K f ≤ B ∧
        nativeLieExponential (I := I) (G := G) ((K f : ℝ) • V f) ∈ Γ := by
  have h : ∀ f : ↥(nativeSmoothBasisIntegerCharacterGrid (I := I) Γ B),
      ∃ (V : E) (K : ℕ), V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧
        f.val V = 1 ∧ 0 < K ∧ K ≤ B ∧
        nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
    intro f
    exact native_smooth_integer_grid_bounded_normalization Γ B f.property
  choose V K hV hv hk hB hΓ using h
  exact ⟨V, K, fun f => ⟨hV f, hv f, hk f, hB f, hΓ f⟩⟩

end Hindman168
