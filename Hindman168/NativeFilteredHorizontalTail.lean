import Hindman168.NativeFilteredSmoothBasisIntegerCharacters
import Hindman168.NativeLatticeFilteredLayerDimensions

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_filtered_horizontal_iff_tail_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ f.ker ↔
      ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val →
        f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i) = 0 := by
  have hs := native_lattice_filtered_layer_start_spec (I := I) Γ 1
  constructor
  · intro hf i hi
    exact hf ((hs.2.1 i).mpr hi)
  · intro hf
    rw [← hs.2.2]
    apply Submodule.span_le.mpr
    rintro v ⟨i, hi, rfl⟩
    exact hf i hi

theorem native_filtered_integer_horizontal_iff_tail_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a).ker ↔
      ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val → a i = 0 := by
  rw [native_filtered_horizontal_iff_tail_zero (I := I) Γ]
  simp only [native_filtered_smooth_basis_integer_functional_basis, Int.cast_eq_zero]

theorem native_filtered_integer_character_iff_head_nonzero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    RoughNativeHorizontalFunctional (E := E) (I := I) Γ
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a) ↔
      a ≠ 0 ∧ ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val → a i = 0 := by
  rw [native_filtered_smooth_basis_integer_functional_horizontal_iff (I := I) Γ,
    native_filtered_integer_horizontal_iff_tail_zero (I := I) Γ]

theorem native_filtered_horizontal_integer_representation (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f) :
    ∃! a : Fin (Module.finrank ℝ E) → ℤ,
      nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a = f ∧ a ≠ 0 ∧
        ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val → a i = 0 := by
  obtain ⟨a, ha, huniq⟩ := native_filtered_smooth_basis_horizontal_integer_representation (I := I) Γ f hf
  have hh : RoughNativeHorizontalFunctional (E := E) (I := I) Γ
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a) := ha.symm ▸ hf
  obtain ⟨hne, htail⟩ := (native_filtered_integer_character_iff_head_nonzero (I := I) Γ a).mp hh
  exact ⟨a, ⟨ha, hne, htail⟩, fun c hc => huniq c hc.1⟩

end Hindman168
