import Hindman168.CompactTorusPeakApproximation

/-! Fixed Fourier kernels give exact finite sums of actual Fourier integrals. -/

namespace Hindman168
open MeasureTheory
open scoped Classical

theorem unit_torus_fourier_kernel_evaluation {κ : Type*} [Fintype κ]
    (c : (κ → ℤ) →₀ ℂ) (F : C(UnitAddTorus κ, ℂ)) :
    unitTorusKernelEvaluation (c.sum (fun k a => a • UnitAddTorus.mFourier k)) F =
      c.sum (fun k a => a * (∫ t : UnitAddTorus κ, UnitAddTorus.mFourier k t * F t
        ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle))) := by
  simp only [unitTorusKernelEvaluation, Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro k _
    exact unit_torus_kernel_evaluation_integrable ((c k) • UnitAddTorus.mFourier k) F

theorem compact_torus_fourier_kernel_reconstruction {κ : Type*} [Fintype κ]
    (H : Set C(UnitAddTorus κ, ℂ)) (hH : IsCompact H)
    (hbound : ∀ F ∈ H, ‖F‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : (κ → ℤ) →₀ ℂ, ∀ F ∈ H,
      ‖F 0 - c.sum (fun k a => a * (∫ t : UnitAddTorus κ, UnitAddTorus.mFourier k t * F t
        ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)))‖ < ε := by
  obtain ⟨n, hn⟩ := compact_torus_peak_kernel_approximation H hH (ε/3) (by positivity)
  obtain ⟨c, hc⟩ := unit_torus_fourier_uniform_approximation κ (unitTorusPeakKernel κ n) (ε/3)
    (by positivity)
  let P : C(UnitAddTorus κ, ℂ) := c.sum (fun k a => a • UnitAddTorus.mFourier k)
  refine ⟨c, ?_⟩
  intro F hF
  have h1 : ‖F 0 - unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F‖ < ε/3 := by
    rw [norm_sub_rev]
    exact hn F hF
  have h2 : ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F - unitTorusKernelEvaluation P F‖ < ε/3 := by
    rw [← unit_torus_kernel_evaluation_kernel_sub]
    apply lt_of_le_of_lt (unit_torus_kernel_evaluation_sup_bound _ _)
    have hb := mul_le_mul_of_nonneg_left (hbound F hF) (norm_nonneg (unitTorusPeakKernel κ n-P))
    have hb' : ‖unitTorusPeakKernel κ n-P‖*‖F‖ ≤ ‖unitTorusPeakKernel κ n-P‖ := by
      simpa only [mul_one] using hb
    exact hb'.trans_lt hc
  rw [← unit_torus_fourier_kernel_evaluation]
  change ‖F 0-unitTorusKernelEvaluation P F‖ < ε
  have ht := dist_triangle (F 0) (unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F)
    (unitTorusKernelEvaluation P F)
  simp only [dist_eq_norm] at ht
  linarith only [ht, h1, h2, hε]

end Hindman168
