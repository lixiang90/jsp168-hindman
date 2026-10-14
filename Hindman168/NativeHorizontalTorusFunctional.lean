import Hindman168.NativeFilteredHorizontalCharacterCoordinates
import Hindman168.RoughBasisFunctionalNorm
import Hindman168.RoughVectorMvPolynomial

/-! Integer Fourier vectors give genuine continuous linear horizontal
characters for the original lattice, with a fixed basis operator budget. -/

namespace Hindman168
open Module
open scoped Classical BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeHorizontalTorusFunctional (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ) : E →L[ℝ] ℝ :=
  ∑ i, (v i : ℝ) • ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val).toContinuousLinearMap

theorem native_horizontal_torus_functional_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ) (x : E) :
    nativeHorizontalTorusFunctional (I := I) Γ v x =
      ∑ i, (v i : ℝ)*(nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr x i.val := by
  simp only [nativeHorizontalTorusFunctional, sum_apply,
    smul_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply, smul_eq_mul]

theorem native_horizontal_torus_functional_basis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ)
    (i : ↥(nativeFilteredHorizontalIndices (I := I) Γ)) :
    nativeHorizontalTorusFunctional (I := I) Γ v
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val) = (v i : ℝ) := by
  rw [native_horizontal_torus_functional_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Basis.repr_self, Finsupp.single_eq_same, mul_one]
  · intro j _ hji
    have hv : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp only [Basis.repr_self, Finsupp.single_apply, if_neg hv.symm, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem native_horizontal_torus_functional_horizontal (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ) (hv : v ≠ 0) :
    RoughNativeHorizontalFunctional (E := E) (I := I) Γ
      (nativeHorizontalTorusFunctional (I := I) Γ v).toLinearMap := by
  have hcomm : nativeLieLowerCentralModel (I := I) (G := G) 1 ≤
      (nativeHorizontalTorusFunctional (I := I) Γ v).toLinearMap.ker := by
    intro x hx
    change nativeHorizontalTorusFunctional (I := I) Γ v x = 0
    rw [native_horizontal_torus_functional_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hz := native_filtered_horizontal_coord_functional (I := I) Γ i hx
    change (nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr x i.val = 0 at hz
    rw [hz, mul_zero]
  refine ⟨?_, hcomm, ?_⟩
  · intro hz
    apply hv
    funext i
    apply Int.cast_injective (α := ℝ)
    have hb := congrArg (fun f : E →ₗ[ℝ] ℝ => f
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val)) hz
    change nativeHorizontalTorusFunctional (I := I) Γ v
      (nativeLatticeFilteredSmoothRealBasis (I := I) Γ i.val) = 0 at hb
    rw [native_horizontal_torus_functional_basis] at hb
    simpa only [Pi.zero_apply, Int.cast_zero] using hb
  · intro γ hγ
    have hi := (native_filtered_horizontal_lattice_image_mem_iff (I := I) Γ _).mp ⟨γ, hγ, rfl⟩
    choose a ha using hi
    refine ⟨∑ i, v i*a i, ?_⟩
    change nativeHorizontalTorusFunctional (I := I) Γ v
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = _
    rw [native_horizontal_torus_functional_apply]
    change (∑ i, (v i : ℝ)*nativeFilteredHorizontalCoordinates (I := I) Γ γ i) = _
    simp only [ha, Int.cast_sum, Int.cast_mul]

theorem native_horizontal_torus_functional_norm (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ) :
    ‖nativeHorizontalTorusFunctional (I := I) Γ v‖ ≤
      roughBasisOperatorNormBudget (nativeLatticeFilteredSmoothRealBasis (I := I) Γ)*
        (∑ i, (v i).natAbs : ℕ) := by
  apply rough_basis_values_operator_norm _ _ (Nat.cast_nonneg _)
  intro j
  rw [← Real.norm_eq_abs, native_horizontal_torus_functional_apply]
  calc
    _ ≤ ∑ i, ‖(v i : ℝ)*(nativeLatticeFilteredSmoothRealBasis (I := I) Γ).repr
        (nativeLatticeFilteredSmoothRealBasis (I := I) Γ j) i.val‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((v i).natAbs : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · change ‖(v i : ℝ)*1‖ ≤ ((v i).natAbs : ℝ)
        simpa only [mul_one, Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs] using
          (le_rfl : |(v i : ℝ)| ≤ |(v i : ℝ)|)
      · simp only [mul_zero, norm_zero]
        exact Nat.cast_nonneg _
    _ = _ := by rw [Nat.cast_sum]

theorem native_horizontal_torus_functional_polynomial {σ : Type*}
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : ↥(nativeFilteredHorizontalIndices (I := I) Γ) → ℤ)
    (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvProjection (nativeHorizontalTorusFunctional (I := I) Γ v).toLinearMap p =
      ∑ i, MvPolynomial.C (v i : ℝ)*roughVectorMvProjection
        ((nativeLatticeFilteredSmoothRealBasis (I := I) Γ).coord i.val) p := by
  induction p with
  | nil => simp only [roughVectorMvProjection, mul_zero, Finset.sum_const_zero]
  | cons a p ih =>
    simp only [roughVectorMvProjection, ContinuousLinearMap.coe_coe, native_horizontal_torus_functional_apply,
      ih, map_sum, map_mul, Finset.mul_sum,
      mul_add, Finset.sum_add_distrib, Basis.coord_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end Hindman168
