import Hindman168.RoughNativeCommutatorBasis
import Hindman168.RoughNativeBasisCharacterGrid

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_horizontal_commutator_basis_zero (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ χ.ker)
    (i : Fin (Module.finrank ℚ (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ))) :
    χ (roughNativeCommutatorBasis (E := E) (I := I) Γ (Sum.inl i)) = 0 :=
  hχ (rough_native_commutator_basis_inl_mem Γ i)

theorem rough_native_horizontal_complement_values_bound (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤ χ.ker)
    (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ i, |χ (roughNativeCommutatorBasis (E := E) (I := I) Γ (Sum.inr i))| ≤ M) :
    ∀ i, |χ (roughNativeCommutatorBasis (E := E) (I := I) Γ i)| ≤ M := by
  intro i
  cases i with
  | inl i => simpa only [rough_native_horizontal_commutator_basis_zero Γ χ hχ i, abs_zero] using hM
  | inr i => exact hv i

theorem rough_native_horizontal_complement_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M) (χ : E →L[ℝ] ℝ)
    (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap)
    (hv : ∀ i, |χ (roughNativeCommutatorBasis (E := E) (I := I) Γ (Sum.inr i))| ≤ M) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ
      (roughBasisOperatorNormBudget (roughNativeCommutatorBasis (E := E) (I := I) Γ)*M) :=
  rough_native_basis_bounded_horizontal_grid_mem Γ _ M hM χ
    (rough_native_horizontal_complement_values_bound Γ χ.toLinearMap hhor.2.1 M hM hv) hhor

theorem rough_native_commutator_integer_size_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M) (χ : E →L[ℝ] ℝ)
    (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap)
    (m : RoughNativeCommutatorBasisIndex (E := E) (I := I) Γ → ℤ)
    (hm : ∀ i ∈ roughNativeCommutatorHorizontalIndices (E := E) (I := I) Γ,
      χ (roughNativeCommutatorBasis (E := E) (I := I) Γ i) = (m i : ℝ))
    (hsize : ∑ i ∈ roughNativeCommutatorHorizontalIndices (E := E) (I := I) Γ,
      (m i : ℝ)^2 ≤ M^2) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ
      (roughBasisOperatorNormBudget (roughNativeCommutatorBasis (E := E) (I := I) Γ)*M) :=
  rough_native_horizontal_integer_size_grid_mem Γ _ _
    (rough_native_commutator_basis_outside_horizontal Γ) M hM χ hhor m hm hsize

end Hindman168
