import Mathlib.Analysis.Calculus.MeanValue

/-! A genuine uniform quadratic remainder from a Lipschitz derivative
on a convex domain, derived by the mean value estimate on the actual
segment between the two original points. -/

namespace Hindman168
open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem norm_derivative_remainder_le {f : E → F} {D : E → E →L[ℝ] F}
    {U : Set E} (hU : Convex ℝ U) (hD : ∀ z ∈ U, HasFDerivAt f (D z) z)
    {C : ℝ≥0} (hLip : LipschitzOnWith C D U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f y - f x - D x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hd (z : E) (hz : z ∈ segment ℝ x y) :
      HasFDerivWithinAt (fun w => f w - D x w) (D z - D x) (segment ℝ x y) z :=
    ((hD z (hU.segment_subset hx hy hz)).sub (D x).hasFDerivAt).hasFDerivWithinAt
  have hb (z : E) (hz : z ∈ segment ℝ x y) :
      ‖D z - D x‖ ≤ (C : ℝ) * ‖y - x‖ := by
    have hzball : z ∈ closedBall x ‖y - x‖ :=
      (convex_closedBall x ‖y - x‖).segment_subset
        (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm]) hz
    have hzbound : ‖z - x‖ ≤ ‖y - x‖ := by simpa only [mem_closedBall, dist_eq_norm] using hzball
    exact (hLip.norm_sub_le (hU.segment_subset hx hy hz) hx).trans
      (mul_le_mul_of_nonneg_left hzbound C.coe_nonneg)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : (f y - D x y) - (f x - D x x) = f y - f x - D x (y - x) := by
    rw [map_sub]
    abel
  rw [heq] at h
  simpa only [pow_two, mul_assoc] using h

end Hindman168
