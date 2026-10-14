import Hindman168.UnitCircleLinearInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace Hindman168
open scoped Topology
open MeasureTheory

noncomputable def unitCircleNormBump (c : ℝ) : UnitAddCircle → ℝ :=
  fun t => max 0 (c-‖t‖)

theorem unit_circle_norm_bump_nonneg (c : ℝ) (t : UnitAddCircle) :
    0 ≤ unitCircleNormBump c t := le_max_left _ _

theorem unit_circle_norm_bump_le (c : ℝ) (hc : 0 ≤ c) (t : UnitAddCircle) :
    unitCircleNormBump c t ≤ c := by
  exact max_le hc (sub_le_self _ (norm_nonneg _))

theorem unit_circle_norm_bump_lipschitz (c : ℝ) : LipschitzWith 1 (unitCircleNormBump c) := by
  have h : LipschitzWith 1 (fun t : UnitAddCircle => c-‖t‖) := by
    apply LipschitzWith.mk_one
    intro t u
    simpa only [Real.dist_eq, sub_sub_sub_cancel_left, Real.norm_eq_abs, abs_sub_comm,
      dist_eq_norm] using
      abs_norm_sub_norm_le t u
  exact h.const_max 0

noncomputable def unitCircleNormBumpObservable (c : ℝ) : C(UnitAddCircle, ℂ) :=
  ⟨fun t => (unitCircleNormBump c t : ℂ),
    Complex.continuous_ofReal.comp (unit_circle_norm_bump_lipschitz c).continuous⟩

theorem unit_circle_norm_bump_observable_admissible (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitCircleNormBumpObservable c ∈ unitLipschitzObservables UnitAddCircle := by
  refine ⟨?_, ?_⟩
  · apply LipschitzWith.mk_one
    intro t u
    change dist (Complex.ofReal (unitCircleNormBump c t))
      (Complex.ofReal (unitCircleNormBump c u)) ≤ dist t u
    rw [Complex.isometry_ofReal.dist_eq]
    exact (unit_circle_norm_bump_lipschitz c).dist_le_mul t u |>.trans (by simp)
  · intro t
    change ‖(unitCircleNormBump c t : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unit_circle_norm_bump_nonneg c t)]
    exact (unit_circle_norm_bump_le c hc t).trans hc1

theorem unit_circle_haar_closed_ball (c : ℝ) (hc2 : 2*c ≤ 1) :
    AddCircle.haarAddCircle (Metric.closedBall (0 : UnitAddCircle) c) = ENNReal.ofReal (2*c) := by
  have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hv, AddCircle.volume_closedBall, min_eq_right hc2]

theorem unit_circle_norm_bump_haar_bound (c : ℝ) (hc : 0 ≤ c) (hc2 : 2*c ≤ 1) :
    (∫ t, unitCircleNormBump c t ∂AddCircle.haarAddCircle) ≤ 2*c^2 := by
  let s := Metric.closedBall (0 : UnitAddCircle) c
  have hi : Integrable (unitCircleNormBump c) AddCircle.haarAddCircle :=
    (unit_circle_norm_bump_lipschitz c).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (s.indicator (fun _ => c)) AddCircle.haarAddCircle :=
    (integrable_const c).indicator measurableSet_closedBall
  have hle : unitCircleNormBump c ≤ s.indicator (fun _ => c) := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
      exact unit_circle_norm_bump_le c hc t
    · rw [Set.indicator_of_notMem ht]
      have hn : c < ‖t‖ := by
        simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using ht
      exact max_le le_rfl (by linarith)
  have hb := integral_mono hi hg hle
  rw [integral_indicator measurableSet_closedBall, integral_const] at hb
  simp only [Measure.real, Measure.restrict_apply_univ,
    unit_circle_haar_closed_ball c hc2, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*c),
    smul_eq_mul] at hb
  nlinarith

end Hindman168
