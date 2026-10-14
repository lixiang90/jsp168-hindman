import Hindman168.RoughNativeGroupDifferencePolynomial
import Hindman168.RoughFilteredPolynomialRestriction

namespace Hindman168
open scoped Manifold ContDiff

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeIteratedDifferenceMvPolynomial (p : RoughVectorMvPolynomial κ E) :
    List (κ → ℝ) → RoughVectorMvPolynomial κ E
  | [] => p
  | h :: hs => roughNativeGroupDifferenceMvPolynomial (I := I) (G := G) h
      (roughNativeIteratedDifferenceMvPolynomial p hs)

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem rough_native_iterated_difference_weighted (D : ℕ) (hD : 0 < D)
    {p : RoughVectorMvPolynomial κ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) p k)
    (hs : List (κ → ℝ)) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D)
      (roughNativeIteratedDifferenceMvPolynomial (I := I) (G := G) p hs) (k+hs.length) := by
  induction hs with
  | nil => exact hp
  | cons h hs ih =>
      simpa only [roughNativeIteratedDifferenceMvPolynomial, List.length_cons, Nat.add_assoc] using
        rough_native_group_difference_polynomial_weighted D hD h ih

omit [Fintype κ] in
theorem rough_native_iterated_difference_polynomial_eval (p : RoughVectorMvPolynomial κ E)
    (hs : List (κ → ℝ)) (x : κ → ℝ) :
    roughVectorMvEval (E := E) (roughNativeIteratedDifferenceMvPolynomial (I := I) (G := G) p hs) x =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (roughIteratedGroupDifference (fun y =>
          nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p y)) hs x) := by
  induction hs generalizing x with
  | nil => exact (nativeLieGlobalLogarithm_exponential (I := I) (G := G) _).symm
  | cons h hs ih =>
      rw [roughNativeIteratedDifferenceMvPolynomial, rough_native_group_difference_polynomial_eval,
        ih, ih, nativeLieExponential_globalLogarithm, nativeLieExponential_globalLogarithm]
      rfl

theorem rough_native_bounded_log_polynomial_filtered (D : ℕ) (hD : 0 < D)
    {p : RoughVectorMvPolynomial κ E} (hp : RoughVectorMvDegreeLE p D) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G D)
      (fun x : κ → ℝ => nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p x)) := by
  intro hs x
  have hw := rough_native_iterated_difference_weighted (I := I) (G := G) D hD
    (rough_native_weighted_polynomial_initial (I := I) (G := G) D hD hp) hs
  have hm := rough_native_weighted_polynomial_exp_mem (I := I) (G := G) D hD hw x
  rw [rough_native_iterated_difference_polynomial_eval, nativeLieExponential_globalLogarithm] at hm
  simpa only [Nat.zero_add] using hm

theorem rough_native_integer_log_polynomial_filtered (D : ℕ) (hD : 0 < D)
    {p : RoughVectorMvPolynomial κ E} (hp : RoughVectorMvDegreeLE p D) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration G D)
      (fun x : κ → ℤ => nativeLieExponential (I := I) (G := G)
        (roughVectorMvEval (E := E) p (fun j => (x j : ℝ)))) := by
  let c : (κ → ℤ) →+ (κ → ℝ) := {
    toFun := fun x j => (x j : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro x y; funext j; exact Int.cast_add _ _ }
  exact rough_filtered_polynomial_precompose _ _
    (rough_native_bounded_log_polynomial_filtered D hD hp) c

end Hindman168
