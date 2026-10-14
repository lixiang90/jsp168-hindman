import Hindman168.RoughNativeStretchedLieTerminal
import Hindman168.RoughVectorZeroTrim
import Hindman168.RoughNativePolynomialFiltered

namespace Hindman168
open scoped Manifold ContDiff

variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_iterated_difference_uniform_degree (D : ℕ) (hD : 0 < D)
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) {p : RoughVectorMvPolynomial κ E}
    (hp : RoughVectorMvDegreeLE p D) (shifts : List (κ → ℝ)) :
    ∃ r : RoughVectorMvPolynomial κ E,
      RoughVectorMvDegreeLE r (s*D-shifts.length) ∧
      RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D)
        r shifts.length ∧
      ∀ x, roughVectorMvEval r x = nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (roughIteratedGroupDifference (fun y => nativeLieExponential (I := I) (G := G)
          (roughVectorMvEval (E := E) p y)) shifts x) := by
  let r := roughNativeIteratedDifferenceMvPolynomial (I := I) (G := G) p shifts
  have hw : RoughVectorMvWeightedDegree
      (roughNativeStretchedLieFiltration (I := I) (G := G) D) r shifts.length := by
    simpa only [Nat.zero_add] using rough_native_iterated_difference_weighted (I := I) (G := G)
      D hD (rough_native_weighted_polynomial_initial (I := I) (G := G) D hD hp) shifts
  refine ⟨roughVectorMvZeroTrim r,
    rough_vector_zero_trim_degree _ (rough_native_stretched_lie_antitone D hD) hw
      (rough_native_stretched_lie_terminal D hD hs), rough_vector_zero_trim_weighted _ hw, ?_⟩
  intro x
  rw [rough_vector_zero_trim_eval]
  exact rough_native_iterated_difference_polynomial_eval p shifts x

theorem rough_native_iterated_difference_terminal (D : ℕ) (hD : 0 < D)
    {s : ℕ} (hs : Group.nilpotencyClass G ≤ s) {p : RoughVectorMvPolynomial κ E}
    (hp : RoughVectorMvDegreeLE p D) (shifts : List (κ → ℝ))
    (hlen : s*D < shifts.length) (x : κ → ℝ) :
    roughIteratedGroupDifference (fun y => nativeLieExponential (I := I) (G := G)
      (roughVectorMvEval (E := E) p y)) shifts x = 1 := by
  have hm := rough_native_bounded_log_polynomial_filtered (I := I) (G := G) D hD hp shifts x
  rw [rough_stretched_filtration_beyond_terminal D hD hs (by omega), Subgroup.mem_bot] at hm
  exact hm

end Hindman168
