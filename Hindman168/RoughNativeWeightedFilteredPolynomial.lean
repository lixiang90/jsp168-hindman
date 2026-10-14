import Hindman168.RoughNativePolynomialFiltered

/-! The SAME termwise original Lie-filtration weights suffice for genuine
original filtered polynomiality, even when ordinary degree exceeds the
original stretch. This avoids enlarging the induction filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_weighted_log_polynomial_filtered (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial κ E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) d) p 0) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G d)
      (fun x : κ → ℝ => nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p x)) := by
  intro hs x
  have hw := rough_native_iterated_difference_weighted (I := I) (G := G) d hd hp hs
  have hm := rough_native_weighted_polynomial_exp_mem (I := I) (G := G) d hd hw x
  rw [rough_native_iterated_difference_polynomial_eval,nativeLieExponential_globalLogarithm] at hm
  simpa only [Nat.zero_add] using hm

theorem rough_native_integer_weighted_log_polynomial_filtered (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial κ E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) d) p 0) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G d)
      (fun x : κ → ℤ => nativeLieExponential (I := I) (G := G)
        (roughVectorMvEval (E := E) p (fun j => (x j : ℝ)))) := by
  let c : (κ → ℤ) →+ (κ → ℝ) := {
    toFun := fun x j => (x j : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro x y; funext j; exact Int.cast_add _ _ }
  exact rough_filtered_polynomial_precompose _ _
    (rough_native_weighted_log_polynomial_filtered d hd hp) c

end Hindman168
