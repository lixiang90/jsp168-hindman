import Hindman168.NativeFilteredHorizontalTail
import Hindman168.RoughHorizontalIntegerSize

namespace Hindman168
open scoped Classical BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeFilteredHorizontalIndices (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : Finset (Fin (Module.finrank ℝ E)) :=
  Finset.univ.filter (fun i => i.val < nativeLatticeFilteredLayerStart (I := I) Γ 1)

noncomputable def nativeFilteredHorizontalCoefficientSize (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : ↥(nativeFilteredHorizontalIndices (I := I) Γ) =>
    f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val)) :
      EuclideanSpace ℝ ↥(nativeFilteredHorizontalIndices (I := I) Γ))‖

theorem native_filtered_horizontal_indices_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    i ∈ nativeFilteredHorizontalIndices (I := I) Γ ↔
      i.val < nativeLatticeFilteredLayerStart (I := I) Γ 1 := by
  simp only [nativeFilteredHorizontalIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem native_filtered_horizontal_coefficient_size_nonnegative (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) :
    0 ≤ nativeFilteredHorizontalCoefficientSize (I := I) Γ f := norm_nonneg _

theorem native_filtered_horizontal_coefficient_size_square (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) :
    nativeFilteredHorizontalCoefficientSize (I := I) Γ f ^ 2 =
      ∑ i ∈ nativeFilteredHorizontalIndices (I := I) Γ,
        f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i)^2 := by
  unfold nativeFilteredHorizontalCoefficientSize
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_coe_sort (nativeFilteredHorizontalIndices (I := I) Γ)
    (fun i => f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i)^2)

theorem native_filtered_integer_horizontal_size (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ) :
    nativeFilteredHorizontalCoefficientSize (I := I) Γ
      (nativeFilteredSmoothBasisIntegerFunctional (I := I) Γ a) =
        roughHorizontalIntegerSize (nativeFilteredHorizontalIndices (I := I) Γ) a := by
  simp only [nativeFilteredHorizontalCoefficientSize, roughHorizontalIntegerSize,
    native_filtered_smooth_basis_integer_functional_basis]

theorem native_filtered_horizontal_full_integer_size_eq (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (a : Fin (Module.finrank ℝ E) → ℤ)
    (htail : ∀ i, nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val → a i = 0) :
    roughHorizontalIntegerSize Finset.univ a =
      roughHorizontalIntegerSize (nativeFilteredHorizontalIndices (I := I) Γ) a := by
  have hsum : (∑ i ∈ Finset.univ, (a i : ℝ)^2) =
      ∑ i ∈ nativeFilteredHorizontalIndices (I := I) Γ, (a i : ℝ)^2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : nativeLatticeFilteredLayerStart (I := I) Γ 1 ≤ i.val :=
      Nat.le_of_not_gt (fun h => hi ((native_filtered_horizontal_indices_mem_iff (I := I) Γ i).mpr h))
    rw [htail i hn, Int.cast_zero, zero_pow (by decide : 2 ≠ 0)]
  have hsq := rough_horizontal_integer_size_square Finset.univ a
  have hsq' := rough_horizontal_integer_size_square (nativeFilteredHorizontalIndices (I := I) Γ) a
  have hn := rough_horizontal_integer_size_nonnegative Finset.univ a
  have hn' := rough_horizontal_integer_size_nonnegative (nativeFilteredHorizontalIndices (I := I) Γ) a
  exact (sq_eq_sq₀ hn hn').mp (hsq.trans (hsum.trans hsq'.symm))

end Hindman168
