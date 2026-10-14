import Hindman168.RoughNativeFunctionalGridBudget
import Hindman168.NativeLieLogarithmCharacter
import Hindman168.NativeLatticeRationalCharacter

namespace Hindman168
open Module
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

def RoughNativeHorizontalFunctional (Γ : Subgroup G) (χ : E →ₗ[ℝ] ℝ) : Prop :=
  χ ≠ 0 ∧ nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ χ.ker ∧
    ∀ γ ∈ Γ, ∃ m : ℤ, χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ)

noncomputable def roughNativeHorizontalCharacterGrid (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) : Finset (E →ₗ[ℝ] ℝ) :=
  (roughNativeFiniteFunctionalGrid (E := E) (I := I) Γ
    ⌈A*roughNativeFunctionalGridBudget (E := E) (I := I) Γ⌉₊).filter
    (RoughNativeHorizontalFunctional (E := E) (I := I) Γ)

theorem rough_native_horizontal_grid_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) (χ : E →ₗ[ℝ] ℝ) :
    χ ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A ↔
      χ ∈ roughNativeFiniteFunctionalGrid (E := E) (I := I) Γ
        ⌈A*roughNativeFunctionalGridBudget (E := E) (I := I) Γ⌉₊ ∧
      RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ := by
  simp only [roughNativeHorizontalCharacterGrid, Finset.mem_filter]

theorem rough_native_norm_bounded_horizontal_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) (hA : 0 ≤ A) (χ : E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A) (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A :=
  (rough_native_horizontal_grid_mem_iff Γ A χ.toLinearMap).mpr
    ⟨rough_native_norm_bounded_functional_grid_mem Γ A hA χ hχ hhor.2.2, hhor⟩

theorem rough_native_horizontal_grid_character (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) {χ : E →ₗ[ℝ] ℝ}
    (hχ : χ ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A) :
    χ ≠ 0 ∧
      (∀ g h : G, nativeLieLogarithmCharacter (I := I) (G := G) χ (g*h) =
        nativeLieLogarithmCharacter (I := I) (G := G) χ g+
          nativeLieLogarithmCharacter (I := I) (G := G) χ h) ∧
      Function.Surjective (nativeLieLogarithmCharacter (I := I) (G := G) χ) ∧
      ∀ γ ∈ Γ, ∃ m : ℤ, nativeLieLogarithmCharacter (I := I) (G := G) χ γ = (m : ℝ) := by
  have hh := ((rough_native_horizontal_grid_mem_iff Γ A χ).mp hχ).2
  exact ⟨hh.1, nativeLieLogarithmCharacter_mul χ hh.2.1,
    nativeLieLogarithmCharacter_surjective χ hh.1, hh.2.2⟩

theorem rough_native_bracket_integral_norm_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (A : ℝ) (hA : 0 ≤ A) (χ : E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A) (hne : χ.toLinearMap ≠ 0)
    (hbr : ∀ v w : E, χ (nativeLieAdjointDifferential (I := I) (G := G) v w) = 0)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ)) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ A :=
  rough_native_norm_bounded_horizontal_grid_mem Γ A hA χ hχ
    ⟨hne, nativeLieFunctional_lowerCentral_le_kernel χ.toLinearMap hbr, hint⟩

end Hindman168
