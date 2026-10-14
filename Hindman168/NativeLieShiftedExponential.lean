import Hindman168.NativeLieDexpInvertible
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! The original exponential in a genuine inverse-left-translated identity
chart. Its actual derivative at zero is native dexp. Original group
nilpotency therefore supplies a genuine inverse-function theorem here. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieShiftedExponential (v : E) (w : E) : E :=
  nativeLieRelativeCoordinateCurve (I := I) (G := G) v (1, w)

 theorem nativeLieShiftedExponential_zero (v : E) :
    nativeLieShiftedExponential (I := I) (G := G) v 0 = extChartAt I (1 : G) (1 : G) := by
  unfold nativeLieShiftedExponential nativeLieRelativeCoordinateCurve
  rw [nativeLieRelativeCurve_state_zero]

 theorem nativeLieShiftedExponential_contDiffAt (v : E) :
    ContDiffAt ℝ ∞ (nativeLieShiftedExponential (I := I) (G := G) v) (0 : E) := by
  exact (nativeLieRelativeCoordinateCurve_contDiffAt (I := I) (G := G) v 1).comp (0 : E)
    (contDiffAt_const.prodMk contDiffAt_id)

 theorem nativeLieShiftedExponential_hasFDerivAt (v : E) :
    HasFDerivAt (nativeLieShiftedExponential (I := I) (G := G) v)
      (nativeLieDexp (I := I) (G := G) v) (0 : E) := by
  rw [nativeLieDexp_eq_parameterJacobian]
  exact nativeLieRelativeCoordinateCurve_state_hasFDerivAt (I := I) (G := G) v 1

variable [Group.IsNilpotent G]

noncomputable def nativeLieDexpEquiv (v : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofUnit (nativeLieDexp_isUnit (I := I) (G := G) v).unit

 theorem nativeLieDexpEquiv_toContinuousLinearMap (v : E) :
    (nativeLieDexpEquiv (I := I) (G := G) v : E →L[ℝ] E) = nativeLieDexp (I := I) (G := G) v := by
  exact (nativeLieDexp_isUnit (I := I) (G := G) v).unit_spec

 theorem nativeLieShiftedExponential_hasStrictFDerivAt (v : E) :
    HasStrictFDerivAt (nativeLieShiftedExponential (I := I) (G := G) v)
      (nativeLieDexpEquiv (I := I) (G := G) v : E →L[ℝ] E) (0 : E) := by
  rw [nativeLieDexpEquiv_toContinuousLinearMap]
  exact (nativeLieShiftedExponential_contDiffAt (I := I) (G := G) v).hasStrictFDerivAt'
    (nativeLieShiftedExponential_hasFDerivAt v) (by norm_num)

noncomputable def nativeLieShiftedExponentialInverse (v : E) : E → E :=
  (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).localInverse _ _ _

 theorem nativeLieShiftedExponentialInverse_left (v : E) :
    ∀ᶠ w : E in 𝓝 0, nativeLieShiftedExponentialInverse (I := I) (G := G) v
      (nativeLieShiftedExponential (I := I) (G := G) v w) = w :=
  (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).eventually_left_inverse

 theorem nativeLieShiftedExponentialInverse_right (v : E) :
    ∀ᶠ z : E in 𝓝 (extChartAt I (1 : G) (1 : G)),
      nativeLieShiftedExponential (I := I) (G := G) v
        (nativeLieShiftedExponentialInverse (I := I) (G := G) v z) = z := by
  have h := (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).eventually_right_inverse
  rw [nativeLieShiftedExponential_zero] at h
  exact h

 theorem nativeLieShiftedExponentialInverse_center (v : E) :
    nativeLieShiftedExponentialInverse (I := I) (G := G) v (extChartAt I (1 : G) (1 : G)) = 0 := by
  have h := (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).localInverse_apply_image
  rw [nativeLieShiftedExponential_zero] at h
  exact h

 theorem nativeLieShiftedExponentialInverse_hasStrictFDerivAt (v : E) :
    HasStrictFDerivAt (nativeLieShiftedExponentialInverse (I := I) (G := G) v)
      ((nativeLieDexpEquiv (I := I) (G := G) v).symm : E →L[ℝ] E)
        (extChartAt I (1 : G) (1 : G)) := by
  have h := (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).to_localInverse
  rw [nativeLieShiftedExponential_zero] at h
  exact h

 theorem nativeLieShiftedExponentialInverse_contDiffAt (v : E) :
    ContDiffAt ℝ ∞ (nativeLieShiftedExponentialInverse (I := I) (G := G) v)
      (extChartAt I (1 : G) (1 : G)) := by
  have hd : HasFDerivAt (nativeLieShiftedExponential (I := I) (G := G) v)
      (nativeLieDexpEquiv (I := I) (G := G) v : E →L[ℝ] E) (0 : E) :=
    (nativeLieShiftedExponential_hasStrictFDerivAt (I := I) (G := G) v).hasFDerivAt
  have h := (nativeLieShiftedExponential_contDiffAt (I := I) (G := G) v).to_localInverse hd
    (by norm_num : (∞ : ℕ∞ω) ≠ 0)
  rw [nativeLieShiftedExponential_zero] at h
  convert! h using 1

end Hindman168
