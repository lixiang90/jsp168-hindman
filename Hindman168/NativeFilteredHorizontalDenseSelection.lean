import Hindman168.NativeFilteredHorizontalGrid
import Hindman168.FiniteCandidateDenseRows

namespace Hindman168
open scoped BigOperators Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

/-- Bounded actual horizontal outputs admit one common actual functional on
many directions and many origins. The analytic outputs remain an input. -/
theorem native_filtered_horizontal_common_dense_rows {Q X : Type*}
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (M : ℝ) (hM : 0 ≤ M) (T : Finset Q) (S : Finset X)
    (hT : T.Nonempty) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (R : (E →ₗ[ℝ] ℝ) → Q → X → Prop)
    (houtputs : ∀ q ∈ T, δ*(S.card : ℝ) ≤ ((S.filter (fun x =>
      ∃ f : E →ₗ[ℝ] ℝ, RoughNativeHorizontalFunctional (E := E) (I := I) Γ f ∧
        nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M ∧ R f q x)).card : ℝ)) :
    let A := (nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈M⌉₊).filter
      (fun f => nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M)
    ∃ f : E →ₗ[ℝ] ℝ, RoughNativeHorizontalFunctional (E := E) (I := I) Γ f ∧
      nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M ∧
      δ/(2*(A.card : ℝ))*(T.card : ℝ) ≤
        ((T.filter (fun q => δ/(2*(A.card : ℝ))*(S.card : ℝ) ≤
          ((S.filter (R f q)).card : ℝ))).card : ℝ) := by
  dsimp only
  let A := (nativeFilteredSmoothBasisIntegerCharacterGrid (I := I) Γ ⌈M⌉₊).filter
    (fun f => nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M)
  have hrows : ∀ q ∈ T, δ*(S.card : ℝ) ≤
      ((S.filter (fun x => ∃ f ∈ A, R f q x)).card : ℝ) := by
    intro q hq
    refine (houtputs q hq).trans ?_
    have hsub : (S.filter (fun x => ∃ f : E →ₗ[ℝ] ℝ,
        RoughNativeHorizontalFunctional (E := E) (I := I) Γ f ∧
          nativeFilteredHorizontalCoefficientSize (I := I) Γ f ≤ M ∧ R f q x)) ⊆
        S.filter (fun x => ∃ f ∈ A, R f q x) := by
      intro x hx
      obtain ⟨hxS, f, hhor, hsize, hr⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS, f, ?_, hr⟩
      exact Finset.mem_filter.mpr
        ⟨native_filtered_horizontal_size_grid_contains (I := I) Γ M hM f hhor hsize, hsize⟩
    exact_mod_cast Finset.card_le_card hsub
  obtain ⟨f, hf, hd⟩ := finite_candidate_dense_rows T S A hT hS δ hδ R hrows
  obtain ⟨hfgrid, hsize⟩ := Finset.mem_filter.mp hf
  have hhor := ((native_filtered_smooth_basis_integer_grid_mem_iff (I := I) Γ ⌈M⌉₊ f).mp hfgrid).1
  exact ⟨f, hhor, hsize, hd⟩

end Hindman168
