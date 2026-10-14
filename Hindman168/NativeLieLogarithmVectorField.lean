import Hindman168.NativeLieDexpInverseFiltration

/-! The actual logarithm lifting vector field is the genuine finite
inverse of the original exponential differential applied to the desired
original velocity. Actual polynomial operator formulas prove smoothness
and the strict lower-central improvement of parameter differences. -/

namespace Hindman168
open Function Set Topology Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

omit [Group.IsNilpotent G] in
 theorem nativeLieAdjointGenerator_contDiff :
    ContDiff ℝ ∞ (nativeLieAdjointGenerator (I := I) (G := G) : E → E →L[ℝ] E) := by
  have he : (nativeLieAdjointGenerator (I := I) (G := G) : E → E →L[ℝ] E) =
      nativeLieAdjointDifferential (I := I) (G := G) :=
    funext nativeLieAdjointGenerator_eq_differential
  rw [he]
  exact (nativeLieAdjointDifferential (I := I) (G := G)).contDiff

 theorem nativeLieDexp_contDiff :
    ContDiff ℝ ∞ (nativeLieDexp (I := I) (G := G) : E → E →L[ℝ] E) := by
  have he : (nativeLieDexp (I := I) (G := G) : E → E →L[ℝ] E) =
      fun v => ∑ n ∈ range (Group.nilpotencyClass G),
        ((-1 : ℝ) ^ n / ((n + 1).factorial : ℝ)) •
          nativeLieAdjointGenerator (I := I) (G := G) v ^ n :=
    funext nativeLieDexp_finite_formula
  rw [he]
  apply ContDiff.sum
  intro n _
  have hc : ContDiff ℝ ∞
      (fun _ : E => ((-1 : ℝ) ^ n / ((n + 1).factorial : ℝ))) := contDiff_const
  exact hc.smul ((nativeLieAdjointGenerator_contDiff (I := I) (G := G)).pow n)

 theorem nativeLieDexpDefect_contDiff :
    ContDiff ℝ ∞ (nativeLieDexpDefect (I := I) (G := G) : E → E →L[ℝ] E) :=
  contDiff_const.sub (nativeLieDexp_contDiff (I := I) (G := G))

 theorem nativeLieDexpFiniteInverse_contDiff :
    ContDiff ℝ ∞ (nativeLieDexpFiniteInverse (I := I) (G := G) : E → E →L[ℝ] E) := by
  unfold nativeLieDexpFiniteInverse
  apply ContDiff.sum
  intro n _
  exact (nativeLieDexpDefect_contDiff (I := I) (G := G)).pow n

noncomputable def nativeLieLogarithmVectorField (w : E) (v : E) : E :=
  nativeLieDexpFiniteInverse (I := I) (G := G) v w

 theorem nativeLieLogarithmVectorField_contDiff (w : E) :
    ContDiff ℝ ∞ (nativeLieLogarithmVectorField (I := I) (G := G) w) :=
  (nativeLieDexpFiniteInverse_contDiff (I := I) (G := G)).clm_apply contDiff_const

 theorem nativeLieLogarithmVectorField_dexp (w v : E) :
    nativeLieDexp (I := I) (G := G) v
      (nativeLieLogarithmVectorField (I := I) (G := G) w v) = w := by
  have h := congrArg (fun A : E →L[ℝ] E => A w) (nativeLieDexp_mul_finiteInverse (I := I) (G := G) v)
  exact h

 theorem nativeLieLogarithmVectorField_sub_mem_lowerCentral_next (w : E) {v z : E} {j : ℕ}
    (h : v - z ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeLieLogarithmVectorField (I := I) (G := G) w v -
      nativeLieLogarithmVectorField (I := I) (G := G) w z ∈
        nativeLieLowerCentralModel (I := I) (G := G) (j + 1) :=
  nativeLieDexpFiniteInverse_action_sub_mem_lowerCentral_next h w

end Hindman168
