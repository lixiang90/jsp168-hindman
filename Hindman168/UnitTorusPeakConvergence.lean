import Hindman168.UnitTorusKernelEvaluation

/-! The constructed kernels genuinely converge to evaluation at the identity. -/

namespace Hindman168
open MeasureTheory
open scoped Topology

theorem unit_torus_peak_kernel_evaluation_eq {κ : Type*} [Fintype κ]
    (n : ℕ) (F : C(UnitAddTorus κ, ℂ)) :
    unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F =
      (unitTorusPeakMass κ n)⁻¹ •
        (∫ a : UnitAddTorus κ, unitTorusPeakBase κ a ^ n • F a
          ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) := by
  unfold unitTorusKernelEvaluation
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with a
  simp only [unitTorusPeakKernel, ContinuousMap.coe_mk, Complex.ofReal_mul,
    Complex.real_smul, mul_assoc]

theorem unit_torus_peak_kernel_evaluation_tendsto {κ : Type*} [Fintype κ]
    (F : C(UnitAddTorus κ, ℂ)) :
    Filter.Tendsto (fun n => unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F)
      Filter.atTop (𝓝 (F 0)) := by
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
    (x₀ := (0 : UnitAddTorus κ)) (s := Set.univ) isCompact_univ
    (unitTorusPeakBase κ).continuous.continuousOn
    (fun a _ ha => unit_torus_peak_base_unique_maximum a ha)
    (fun a _ => (unit_torus_peak_base_positive a).le)
    (by rw [unit_torus_peak_base_zero]; exact zero_lt_one)
    (by simp) F.continuous.continuousOn
  simpa only [unit_torus_peak_kernel_evaluation_eq, Measure.restrict_univ, unitTorusPeakMass] using h

theorem unit_torus_peak_kernel_evaluation_eventually_close {κ : Type*} [Fintype κ]
    (F : C(UnitAddTorus κ, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F - F 0‖ < ε := by
  simpa only [dist_eq_norm] using
    (unit_torus_peak_kernel_evaluation_tendsto F).eventually (Metric.ball_mem_nhds _ hε)

end Hindman168
