import Hindman168.NativeLieCurveParameterJacobian

/-! The actual relative parameter Jacobian has zero initial value and
identity initial time derivative. The derivative is derived by genuine
mixed differentiation of the actual relative coordinate curve. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieRelativeCoordinateCurve_hasDerivAt_time_zero (v w : E) :
    HasDerivAt (fun t : ℝ => nativeLieRelativeCoordinateCurve (I := I) (G := G) v (t, w)) w 0 := by
  have hc : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (1 : G))
      (nativeLieRelativeCurve (I := I) (G := G) v (0, w)) := by
    rw [nativeLieRelativeCurve_time_zero]
    exact mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (1 : G))
  have h := hc.hasMFDerivAt.comp (0 : ℝ)
    (nativeLieRelativeCurve_hasMFDerivAt_time_zero (I := I) (G := G) v w)
  erw [nativeLieRelativeCurve_time_zero, mfderiv_extChartAt_self] at h
  have hf : HasFDerivAt (fun t : ℝ => nativeLieRelativeCoordinateCurve (I := I) (G := G) v (t, w))
      ((ContinuousLinearMap.id ℝ E).comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) 0 := by
    convert! h.hasFDerivAt using 1
  convert! hf.hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]

 theorem nativeLieRelativeCoordinateCurve_time_derivative_eventually (v : E) :
    ∀ᶠ w : E in 𝓝 0,
      fderiv ℝ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v) (0, w) (1, 0) = w := by
  have hf := (nativeLieRelativeCoordinateCurve_contDiffAt (I := I) (G := G) v 0).of_le
    (show (1 : ℕ∞ω) ≤ ∞ from by norm_num)
  have hp : ContinuousAt (fun w : E => ((0 : ℝ), w)) 0 := continuousAt_const.prodMk continuousAt_id
  have he := hp.eventually (hf.eventually (by norm_num : (1 : ℕ∞ω) ≠ ∞))
  filter_upwards [he] with w hw
  have hd := (hw.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 w))
  exact hd.unique (nativeLieRelativeCoordinateCurve_hasDerivAt_time_zero (I := I) (G := G) v w)

 theorem nativeLieCurveParameterJacobian_action_hasDerivAt_zero (v w : E) :
    HasDerivAt (fun t : ℝ => nativeLieCurveParameterJacobian (I := I) (G := G) v t w) w 0 := by
  have h := mixedFlowJacobian_hasDerivAt
    ((nativeLieRelativeCoordinateCurve_contDiffAt (I := I) (G := G) v 0).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (nativeLieRelativeCoordinateCurve_time_derivative_eventually (I := I) (G := G) v) w
  have he : (fun t : ℝ => nativeLieCurveParameterJacobian (I := I) (G := G) v t w) =
      (fun t => fderiv ℝ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v) (t, 0) (0, w)) := by
    funext t
    rw [nativeLieCurveParameterJacobian_eq_coordinate]
    rfl
  rw [← he] at h
  change HasDerivAt (fun t : ℝ => nativeLieCurveParameterJacobian (I := I) (G := G) v t w)
    (fderiv ℝ (id : E → E) 0 w) 0 at h
  simpa only [fderiv_id, ContinuousLinearMap.id_apply] using h

 theorem nativeLieCurveParameterJacobian_hasDerivAt_zero (v : E) :
    HasDerivAt (nativeLieCurveParameterJacobian (I := I) (G := G) v)
      (ContinuousLinearMap.id ℝ E) 0 := by
  let K := nativeLieCurveParameterJacobian (I := I) (G := G) v
  have hd : HasDerivAt K (deriv K 0) 0 :=
    ((nativeLieCurveParameterJacobian_contDiff (I := I) (G := G) v).differentiable (by norm_num) 0).hasDerivAt
  have he : deriv K 0 = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro w
    have h := hd.clm_apply (hasDerivAt_const (0 : ℝ) w)
    have h' := h.unique (nativeLieCurveParameterJacobian_action_hasDerivAt_zero (I := I) (G := G) v w)
    simpa only [map_zero, add_zero, ContinuousLinearMap.id_apply] using h'
  rw [he] at hd
  exact hd

end Hindman168
