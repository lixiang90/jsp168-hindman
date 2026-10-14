import Hindman168.NativeLatticeOrderedRealBasis
import Hindman168.RoughNativeBasisCharacterGrid
import Hindman168.RoughHorizontalIntegerSize

/-! Integral logarithmic functionals have actual integer evaluations on the
fixed ordered lattice basis. A bound on the full evaluation vector supplies
the fixed operator norm grid. No filtration-adapted horizontal coordinate
identification or quantitative character existence is assumed here. -/

namespace Hindman168
open Module
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_lattice_ordered_integral_evaluations (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ))
    (i : Fin (Module.finrank ℝ E)) :
    ∃ m : ℤ, χ (nativeLatticeOrderedRealBasis (I := I) Γ i) = (m : ℝ) := by
  have he := hint _ (native_lattice_ordered_basis_exponential_mem (I := I) Γ i)
  simpa only [nativeLieGlobalLogarithm_exponential] using he

noncomputable def nativeLatticeOrderedIntegerEvaluations (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ)) :
    Fin (Module.finrank ℝ E) → ℤ :=
  fun i => Classical.choose (native_lattice_ordered_integral_evaluations Γ χ hint i)

theorem native_lattice_ordered_integer_evaluations_spec (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ))
    (i : Fin (Module.finrank ℝ E)) :
    χ (nativeLatticeOrderedRealBasis (I := I) Γ i) =
      (nativeLatticeOrderedIntegerEvaluations (I := I) Γ χ hint i : ℝ) :=
  Classical.choose_spec (native_lattice_ordered_integral_evaluations Γ χ hint i)

theorem native_lattice_ordered_integer_evaluations_unique (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ))
    (m : Fin (Module.finrank ℝ E) → ℤ)
    (hm : ∀ i, χ (nativeLatticeOrderedRealBasis (I := I) Γ i) = (m i : ℝ)) :
    nativeLatticeOrderedIntegerEvaluations (I := I) Γ χ hint = m := by
  funext i
  apply Int.cast_injective (α := ℝ)
  exact (native_lattice_ordered_integer_evaluations_spec Γ χ hint i).symm.trans (hm i)

theorem native_lattice_ordered_integer_evaluations_zero_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (χ : E →ₗ[ℝ] ℝ)
    (hint : ∀ γ ∈ Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ) = (m : ℝ)) :
    nativeLatticeOrderedIntegerEvaluations (I := I) Γ χ hint = 0 ↔ χ = 0 := by
  constructor
  · intro hm
    apply (nativeLatticeOrderedRealBasis (I := I) Γ).ext
    intro i
    rw [native_lattice_ordered_integer_evaluations_spec Γ χ hint i, hm]
    simp only [Pi.zero_apply, Int.cast_zero, LinearMap.zero_apply]
  · intro hχ
    apply native_lattice_ordered_integer_evaluations_unique Γ χ hint 0
    intro i
    rw [hχ]
    simp only [Pi.zero_apply, Int.cast_zero, LinearMap.zero_apply]

theorem rough_native_ordered_integer_size_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (M : ℝ) (hM : 0 ≤ M)
    (χ : E →L[ℝ] ℝ)
    (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap)
    (hsize : roughHorizontalIntegerSize Finset.univ
      (nativeLatticeOrderedIntegerEvaluations (I := I) Γ χ.toLinearMap hhor.2.2) ≤ M) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ
      (roughBasisOperatorNormBudget (nativeLatticeOrderedRealBasis (I := I) Γ)*M) := by
  apply rough_native_horizontal_integer_size_grid_mem Γ _ Finset.univ
    (by intro i hi; exact (hi (Finset.mem_univ i)).elim) M hM χ hhor
    (nativeLatticeOrderedIntegerEvaluations (I := I) Γ χ.toLinearMap hhor.2.2)
    (by intro i _; exact native_lattice_ordered_integer_evaluations_spec Γ χ.toLinearMap hhor.2.2 i)
  exact (rough_horizontal_integer_size_le_iff _ _ M hM).mp hsize

end Hindman168
