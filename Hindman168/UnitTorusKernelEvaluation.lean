import Hindman168.UnitTorusPeakKernel

/-! Actual kernel evaluation, its true uniform bounds and exact Fourier formula. -/

namespace Hindman168
open MeasureTheory
open scoped Topology

noncomputable def unitTorusKernelEvaluation {κ : Type*} [Fintype κ]
    (K F : C(UnitAddTorus κ, ℂ)) : ℂ :=
  ∫ a : UnitAddTorus κ, K a * F a ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)

theorem unit_torus_kernel_evaluation_integrable {κ : Type*} [Fintype κ]
    (K F : C(UnitAddTorus κ, ℂ)) :
    Integrable (fun a => K a * F a) (Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) :=
  (K.continuous.mul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem unit_torus_kernel_evaluation_sub {κ : Type*} [Fintype κ]
    (K F G : C(UnitAddTorus κ, ℂ)) :
    unitTorusKernelEvaluation K (F-G) = unitTorusKernelEvaluation K F - unitTorusKernelEvaluation K G := by
  simp only [unitTorusKernelEvaluation, ContinuousMap.sub_apply, mul_sub]
  exact integral_sub (unit_torus_kernel_evaluation_integrable K F)
    (unit_torus_kernel_evaluation_integrable K G)

theorem unit_torus_kernel_evaluation_kernel_sub {κ : Type*} [Fintype κ]
    (K L F : C(UnitAddTorus κ, ℂ)) :
    unitTorusKernelEvaluation (K-L) F = unitTorusKernelEvaluation K F - unitTorusKernelEvaluation L F := by
  simp only [unitTorusKernelEvaluation, ContinuousMap.sub_apply, sub_mul]
  exact integral_sub (unit_torus_kernel_evaluation_integrable K F)
    (unit_torus_kernel_evaluation_integrable L F)

theorem unit_torus_kernel_evaluation_sup_bound {κ : Type*} [Fintype κ]
    (K F : C(UnitAddTorus κ, ℂ)) : ‖unitTorusKernelEvaluation K F‖ ≤ ‖K‖*‖F‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
    (Filter.Eventually.of_forall (fun a => show ‖K a * F a‖ ≤ ‖K‖*‖F‖ by
      rw [norm_mul]
      exact mul_le_mul (K.norm_coe_le_norm a) (F.norm_coe_le_norm a) (norm_nonneg _) (norm_nonneg _)))
  simpa only [unitTorusKernelEvaluation, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

theorem unit_torus_peak_kernel_evaluation_bound {κ : Type*} [Fintype κ]
    (n : ℕ) (F : C(UnitAddTorus κ, ℂ)) :
    ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F‖ ≤ ‖F‖ := by
  let μ : Measure (UnitAddTorus κ) := Measure.pi (fun _ : κ => AddCircle.haarAddCircle)
  have hi : Integrable (fun a => ‖unitTorusPeakKernel κ n a‖*‖F‖) μ :=
    ((unitTorusPeakKernel κ n).continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ a, ‖unitTorusPeakKernel κ n a * F a‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ‖unitTorusPeakKernel κ n a‖*‖F‖ ∂μ := by
      apply integral_mono (unit_torus_kernel_evaluation_integrable _ _).norm hi
      intro a
      change ‖unitTorusPeakKernel κ n a * F a‖ ≤ ‖unitTorusPeakKernel κ n a‖ * ‖F‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm a) (norm_nonneg _)
    _ = ‖F‖ := by rw [integral_mul_const, unit_torus_peak_kernel_norm_integral, one_mul]

end Hindman168
