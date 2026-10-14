import Hindman168.CurvePointwiseOperator
import Hindman168.QuadraticDerivativeRemainder

/-! Actual superposition derivatives at nonconstant continuous curves.
A genuine Lipschitz field derivative on an original convex ball yields
a uniform quadratic remainder in the original curve supremum norm. -/

namespace Hindman168
open Set Metric Filter Asymptotics Topology
open scoped NNReal

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem curveSuperposition_quadratic_remainder {f : E → F} {D : E → E →L[ℝ] F}
    {U : Set E} (hU : Convex ℝ U) (hD : ∀ z ∈ U, HasFDerivAt f (D z) z)
    {C : ℝ≥0} (hLip : LipschitzOnWith C D U) (α β : C(K, E))
    (hα : ∀ t, α t ∈ U) (hβ : ∀ t, β t ∈ U) :
    ‖curveSuperposition f β - curveSuperposition f α -
      curveApplyLinear (curveSuperposition D α) (β - α)‖ ≤
      (C : ℝ) * ‖β - α‖ ^ 2 := by
  have hf : ContinuousOn f U := fun z hz => (hD z hz).continuousAt.continuousWithinAt
  have hcα := continuousOn_univ.mp (hf.comp α.continuous.continuousOn (fun t _ => hα t))
  have hcβ := continuousOn_univ.mp (hf.comp β.continuous.continuousOn (fun t _ => hβ t))
  have hcD := continuousOn_univ.mp (hLip.continuousOn.comp α.continuous.continuousOn (fun t _ => hα t))
  apply (ContinuousMap.norm_le _ (mul_nonneg C.coe_nonneg (sq_nonneg _))).mpr
  intro t
  change ‖curveSuperposition f β t - curveSuperposition f α t -
    curveSuperposition D α t (β t - α t)‖ ≤ (C : ℝ) * ‖β - α‖ ^ 2
  rw [curveSuperposition_apply_of_continuous f β hcβ,
    curveSuperposition_apply_of_continuous f α hcα,
    curveSuperposition_apply_of_continuous D α hcD]
  have h := norm_derivative_remainder_le hU hD hLip (hα t) (hβ t)
  have ht : ‖β t - α t‖ ≤ ‖β - α‖ := (β - α).norm_coe_le_norm t
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht 2) C.coe_nonneg)

 theorem curveSuperposition_hasFDerivAt_ball {f : E → F} {D : E → E →L[ℝ] F}
    {x : E} {r : ℝ} (hr : 0 < r)
    (hD : ∀ z ∈ ball x r, HasFDerivAt f (D z) z)
    {C : ℝ≥0} (hLip : LipschitzOnWith C D (ball x r))
    (α : C(K, E)) (hα : ∀ t, α t ∈ ball x (r / 2)) :
    HasFDerivAt (curveSuperposition f)
      (curveApplyLinear (curveSuperposition D α)) α := by
  have hα' (t : K) : α t ∈ ball x r := by
    have ht : dist (α t) x < r / 2 := hα t
    change dist (α t) x < r
    linarith
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  let δ := min (r / 2) (ε / ((C : ℝ) + 1))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [ball_mem_nhds α hδ] with β hβ
  have hβ' (t : K) : β t ∈ ball x r := by
    have ht : dist (β t) (α t) < r / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t)
        (lt_of_lt_of_le hβ (min_le_left _ _))
    exact lt_of_le_of_lt (dist_triangle _ _ _) (by have ha : dist (α t) x < r / 2 := hα t; linarith)
  have h := curveSuperposition_quadratic_remainder (convex_ball x r) hD hLip α β hα' hβ'
  have hn : ‖β - α‖ < ε / ((C : ℝ) + 1) := by
    rw [mem_ball, dist_eq_norm] at hβ
    exact lt_of_lt_of_le hβ (min_le_right _ _)
  have hbound : (C : ℝ) * ‖β - α‖ ≤ ε := by
    have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ) < (C : ℝ) + 1)).mp hn
    have hnorm := norm_nonneg (β - α)
    nlinarith
  exact h.trans (by simpa only [pow_two, ← mul_assoc] using
    mul_le_mul_of_nonneg_right hbound (norm_nonneg (β - α)))

end Hindman168
