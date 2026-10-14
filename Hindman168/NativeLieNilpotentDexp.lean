import Hindman168.NativeLieExponentialDifferential
import Hindman168.AdjointPrimitivePolynomial

/-! The genuine native exponential differential has a finite formula
under original group nilpotency. The cutoff is the original group class,
not an independently supplied native Lie nilpotency assumption. -/

namespace Hindman168
open Function Set Finset Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieCurveParameterJacobian_eq_polynomial [Group.IsNilpotent G] (v : E) (t : ℝ) :
    nativeLieCurveParameterJacobian (I := I) (G := G) v t =
      adjointPrimitivePolynomial (nativeLieAdjointGenerator (I := I) (G := G) v)
        (Group.nilpotencyClass G) t := by
  apply eq_adjointPrimitivePolynomial_of_hasDerivAt _ _ (nativeLieCurveParameterJacobian_zero v)
  intro s
  have h := nativeLieCurveParameterJacobian_hasDerivAt (I := I) (G := G) v s
  rw [nativeLieAdjointCurve_finite_formula_of_group_isNilpotent] at h
  exact h

 theorem nativeLieDexp_finite_formula [Group.IsNilpotent G] (v : E) :
    nativeLieDexp (I := I) (G := G) v =
      ∑ j ∈ range (Group.nilpotencyClass G),
        ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          nativeLieAdjointGenerator (I := I) (G := G) v ^ j := by
  rw [nativeLieDexp_eq_parameterJacobian, nativeLieCurveParameterJacobian_eq_polynomial]
  simp only [adjointPrimitivePolynomial, one_pow, mul_one]

end Hindman168
