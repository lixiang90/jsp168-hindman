import Hindman168.RoughFiniteFunctionalGrid
import Hindman168.RoughNativeCharacterBasisMultipliers

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeFiniteFunctionalGrid (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) : Finset (E →ₗ[ℝ] ℝ) :=
  roughFiniteFunctionalGrid (nativeLatticeRealBasis (E := E) (I := I) Γ)
    (roughNativeCharacterBasisMultiplier (E := E) (I := I) Γ) B

theorem rough_native_finite_functional_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (B : ℕ) (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ))
    (hbound : ∀ i : Fin (Module.finrank ℝ E),
      |χ (roughNativeCharacterBasisVector (E := E) (I := I) Γ i)| ≤ (B : ℝ)) :
    χ ∈ roughNativeFiniteFunctionalGrid (E := E) (I := I) Γ B := by
  apply rough_finite_functional_grid_mem _ _
    (rough_native_character_basis_multiplier_positive (E := E) (I := I) Γ) B χ _ hbound
  intro i
  have hi := hint _ (rough_native_character_basis_vector_exp_mem (E := E) (I := I) Γ i)
  rw [nativeLieGlobalLogarithm_exponential] at hi
  exact hi

end Hindman168
