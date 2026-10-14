import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual globally defined Picard iterates for a continuous vector field.
No solution, convergence or termination is assumed. These lemmas only
derive continuity, initial value and the true derivative of each iterate. -/

namespace Hindman168
open MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def continuousPicardIterate (F : E → E) (u : E) : ℕ → ℝ → E
  | 0 => fun _ => u
  | n + 1 => fun t => u + ∫ s in (0 : ℝ)..t, F (continuousPicardIterate F u n s)

 theorem continuousPicardIterate_continuous {F : E → E} (hF : Continuous F)
    (u : E) (n : ℕ) : Continuous (continuousPicardIterate F u n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact continuous_const.add
      (intervalIntegral.differentiable_integral_of_continuous (hF.comp ih)).continuous

omit [CompleteSpace E] in
 theorem continuousPicardIterate_zero (F : E → E) (u : E) (n : ℕ) :
    continuousPicardIterate F u n 0 = u := by
  cases n <;> simp only [continuousPicardIterate, intervalIntegral.integral_same, add_zero]

 theorem continuousPicardIterate_succ_hasDerivAt {F : E → E} (hF : Continuous F)
    (u : E) (n : ℕ) (t : ℝ) :
    HasDerivAt (continuousPicardIterate F u (n + 1))
      (F (continuousPicardIterate F u n t)) t := by
  have hc := hF.comp (continuousPicardIterate_continuous hF u n)
  convert! (hasDerivAt_const t u).add
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt) using 1
  all_goals simp only [zero_add, Function.comp_apply]

 theorem continuousPicardIterate_succ_sub_succ {F : E → E} (hF : Continuous F)
    (u : E) (n : ℕ) (t : ℝ) :
    continuousPicardIterate F u (n + 2) t - continuousPicardIterate F u (n + 1) t =
      ∫ s in (0 : ℝ)..t,
        F (continuousPicardIterate F u (n + 1) s) - F (continuousPicardIterate F u n s) := by
  have h1 : IntervalIntegrable (fun s => F (continuousPicardIterate F u (n + 1) s)) volume 0 t :=
    (hF.comp (continuousPicardIterate_continuous hF u (n + 1))).intervalIntegrable 0 t
  have h0 : IntervalIntegrable (fun s => F (continuousPicardIterate F u n s)) volume 0 t :=
    (hF.comp (continuousPicardIterate_continuous hF u n)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_sub h1 h0]
  change (u + _) - (u + _) = _ - _
  abel

end Hindman168
