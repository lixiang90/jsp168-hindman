import Hindman168.RoughNativeFiniteFunctionalGrid

namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeFunctionalGridBudget (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : ℝ :=
  1+∑ i : Fin (Module.finrank ℝ E), ‖roughNativeCharacterBasisVector (E := E) (I := I) Γ i‖

theorem rough_native_functional_grid_budget_positive (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    0 < roughNativeFunctionalGridBudget (E := E) (I := I) Γ := by
  unfold roughNativeFunctionalGridBudget
  positivity

theorem rough_native_character_basis_vector_norm_le (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    ‖roughNativeCharacterBasisVector (E := E) (I := I) Γ i‖ ≤
      roughNativeFunctionalGridBudget (E := E) (I := I) Γ := by
  have hi := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) =>
      norm_nonneg (roughNativeCharacterBasisVector (E := E) (I := I) Γ j)) (Finset.mem_univ i)
  dsimp [roughNativeFunctionalGridBudget]
  linarith

theorem rough_native_norm_bounded_functional_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) (hA : 0 ≤ A) (χ : E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ)) :
    χ.toLinearMap ∈ roughNativeFiniteFunctionalGrid (E := E) (I := I) Γ
      ⌈A*roughNativeFunctionalGridBudget (E := E) (I := I) Γ⌉₊ := by
  apply rough_native_finite_functional_grid_mem Γ _ χ.toLinearMap hint
  intro i
  have hn := rough_native_character_basis_vector_norm_le (E := E) (I := I) Γ i
  calc
    |χ (roughNativeCharacterBasisVector (E := E) (I := I) Γ i)| ≤
        ‖χ‖*‖roughNativeCharacterBasisVector (E := E) (I := I) Γ i‖ := by
      simpa only [Real.norm_eq_abs] using χ.le_opNorm _
    _ ≤ A*roughNativeFunctionalGridBudget (E := E) (I := I) Γ :=
      mul_le_mul hχ hn (norm_nonneg _) hA
    _ ≤ _ := Nat.le_ceil _

end Hindman168
