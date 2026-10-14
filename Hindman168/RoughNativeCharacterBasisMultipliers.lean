import Hindman168.NativeLatticeRationalForm
import Hindman168.NativeSubgroupRationalHullRoots

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_character_basis_positive_power (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    ∃ n : ℕ, 0 < n ∧ nativeLieExponential (I := I) (G := G)
      ((n : ℝ) • nativeLatticeRealBasis (E := E) (I := I) Γ i) ∈ Γ := by
  obtain ⟨n, hn, hΓ⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E)
    (I := I) Γ _).mp (nativeLatticeRealBasis_mem_rationalLogSpan (E := E) (I := I) Γ i)
  exact ⟨n, hn, (nativeLieExponential_nat_smul (I := I) (G := G) _ n) ▸ hΓ⟩

noncomputable def roughNativeCharacterBasisMultiplier (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) : ℕ :=
  Classical.choose (rough_native_character_basis_positive_power (E := E) (I := I) Γ i)

theorem rough_native_character_basis_multiplier_positive (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    0 < roughNativeCharacterBasisMultiplier (E := E) (I := I) Γ i :=
  (Classical.choose_spec (rough_native_character_basis_positive_power (E := E) (I := I) Γ i)).1

noncomputable def roughNativeCharacterBasisVector (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) : E :=
  (roughNativeCharacterBasisMultiplier (E := E) (I := I) Γ i : ℝ) •
    nativeLatticeRealBasis (E := E) (I := I) Γ i

theorem rough_native_character_basis_vector_exp_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    nativeLieExponential (I := I) (G := G) (roughNativeCharacterBasisVector (E := E) (I := I) Γ i) ∈ Γ :=
  (Classical.choose_spec (rough_native_character_basis_positive_power (E := E) (I := I) Γ i)).2

end Hindman168
