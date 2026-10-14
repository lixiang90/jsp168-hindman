import Hindman168.NativeLieRelativeCurve

/-! The actual parameter derivative of the genuine relative curve at
zero variation. Coordinate derivatives are identified through the actual
identity chart. Smoothness is proved for the actual operator-valued map. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieCurveParameterJacobian (v : E) (t : ℝ) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ, E) I (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (t, w)) 0

 theorem nativeLieCurveParameterJacobian_zero (v : E) :
    nativeLieCurveParameterJacobian (I := I) (G := G) v 0 = 0 := by
  unfold nativeLieCurveParameterJacobian
  have he : (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (0, w)) =
      (fun _ => (1 : G)) := funext (nativeLieRelativeCurve_time_zero v)
  rw [he, mfderiv_const]
  rfl

 theorem nativeLieRelativeCurve_state_hasMFDerivAt (v : E) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, E) I (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (t, w)) 0
      (nativeLieCurveParameterJacobian (E := E) (I := I) (G := G) v t) := by
  have h : ContMDiff 𝓘(ℝ, E) I ∞
      (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (t, w)) :=
    (nativeLieRelativeCurve_contMDiff (I := I) (G := G) v).comp
      ((contMDiff_const : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun _ : E => t)).prodMk contMDiff_id)
  exact h.mdifferentiableAt (by norm_num) |>.hasMFDerivAt

 theorem nativeLieRelativeCoordinateCurve_state_hasFDerivAt (v : E) (t : ℝ) :
    HasFDerivAt (fun w : E => nativeLieRelativeCoordinateCurve (I := I) (G := G) v (t, w))
      (nativeLieCurveParameterJacobian (I := I) (G := G) v t) 0 := by
  have hc : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (1 : G))
      (nativeLieRelativeCurve (I := I) (G := G) v (t, 0)) := by
    rw [nativeLieRelativeCurve_state_zero]
    exact mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (1 : G))
  have h := hc.hasMFDerivAt.comp (0 : E)
    (nativeLieRelativeCurve_state_hasMFDerivAt (I := I) (G := G) v t)
  erw [nativeLieRelativeCurve_state_zero, mfderiv_extChartAt_self] at h
  have hf : HasFDerivAt (fun w : E => nativeLieRelativeCoordinateCurve (I := I) (G := G) v (t, w))
      ((ContinuousLinearMap.id ℝ E).comp (nativeLieCurveParameterJacobian (I := I) (G := G) v t)) 0 := by
    convert! h.hasFDerivAt using 1
  apply hf.congr_fderiv
  ext w
  rfl

 theorem nativeLieCurveParameterJacobian_eq_coordinate (v : E) (t : ℝ) :
    nativeLieCurveParameterJacobian (I := I) (G := G) v t =
      (fderiv ℝ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v) (t, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hf := (nativeLieRelativeCoordinateCurve_contDiffAt (I := I) (G := G) v t).differentiableAt
    (by norm_num)
  have hc := hf.hasFDerivAt.comp (0 : E)
    ((hasFDerivAt_const t (0 : E)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (0 : E)))
  have h := hc.unique (nativeLieRelativeCoordinateCurve_state_hasFDerivAt (I := I) (G := G) v t)
  exact h.symm

 theorem nativeLieCurveParameterJacobian_contDiff (v : E) :
    ContDiff ℝ ∞ (nativeLieCurveParameterJacobian (I := I) (G := G) v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hf := (nativeLieRelativeCoordinateCurve_contDiffAt (I := I) (G := G) v t).fderiv_right
    (m := ∞) (by simp [ENat.coe_top_add_one])
  have hinr : ContDiffAt ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.inr ℝ ℝ E) t := contDiffAt_const
  have h := (hf.comp t (contDiffAt_id.prodMk contDiffAt_const)).clm_comp hinr
  change ContDiffAt ℝ ∞ (fun s : ℝ =>
    (fderiv ℝ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v) (s, 0)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) t at h
  have he : (fun s : ℝ => (fderiv ℝ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v)
      (s, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E)) =
      nativeLieCurveParameterJacobian (I := I) (G := G) v :=
    funext (fun s => (nativeLieCurveParameterJacobian_eq_coordinate v s).symm)
  rw [he] at h
  exact h

end Hindman168
