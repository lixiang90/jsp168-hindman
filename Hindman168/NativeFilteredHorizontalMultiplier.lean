import Hindman168.NativeFilteredHorizontalGrid

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
theorem native_filtered_horizontal_natural_multiple (Γ : Subgroup G)
    (f : E →ₗ[ℝ] ℝ) (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f)
    (M : ℕ) (hM : 0 < M) :
    RoughNativeHorizontalFunctional (E := E) (I := I) Γ ((M : ℝ) • f) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    exact hf.1 ((smul_eq_zero.mp hz).resolve_left hMr)
  · intro v hv
    change (M : ℝ)*f v = 0
    rw [show f v = 0 from hf.2.1 hv, mul_zero]
  · intro γ hγ
    obtain ⟨n, hn⟩ := hf.2.2 γ hγ
    refine ⟨(M : ℤ)*n, ?_⟩
    change (M : ℝ)*f (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = _
    rw [hn, Int.cast_mul, Int.cast_natCast]

theorem native_filtered_horizontal_size_natural_multiple (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ) (M : ℕ) :
    nativeFilteredHorizontalCoefficientSize (I := I) Γ ((M : ℝ) • f) =
      (M : ℝ)*nativeFilteredHorizontalCoefficientSize (I := I) Γ f := by
  unfold nativeFilteredHorizontalCoefficientSize
  have he : (WithLp.toLp 2 (fun i : ↥(nativeFilteredHorizontalIndices (I := I) Γ) =>
      ((M : ℝ) • f) (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val)) :
        EuclideanSpace ℝ ↥(nativeFilteredHorizontalIndices (I := I) Γ)) =
      (M : ℝ) • (WithLp.toLp 2 (fun i : ↥(nativeFilteredHorizontalIndices (I := I) Γ) =>
        f (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val)) :
          EuclideanSpace ℝ ↥(nativeFilteredHorizontalIndices (I := I) Γ)) := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg M)]

theorem native_filtered_bounded_multiplier_grid_contains (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (f : E →ₗ[ℝ] ℝ)
    (hf : RoughNativeHorizontalFunctional (E := E) (I := I) Γ f)
    (A : ℝ) (hA : 0 ≤ A) (hsize : nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ A)
    (M B : ℕ) (hM : 0 < M) (hMB : M ≤ B) :
    ((M : ℝ) • f) ∈ nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈(B : ℝ)*A⌉₊ := by
  apply native_filtered_horizontal_size_grid_contains (I := I) Γ ((B : ℝ)*A) (by positivity)
    ((M : ℝ) • f) (native_filtered_horizontal_natural_multiple (I := I) Γ f hf M hM)
  rw [native_filtered_horizontal_size_natural_multiple]
  exact (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg M)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hMB) hA)

end Hindman168
