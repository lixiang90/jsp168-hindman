import Hindman168.UnitTorusPeakConvergence

/-! A single actual normalized peak kernel approximates identity evaluation
on an entire compact uniform-norm family, not merely one function at a time. -/

namespace Hindman168
open scoped Topology Classical

theorem compact_torus_peak_kernel_approximation {κ : Type*} [Fintype κ]
    (H : Set C(UnitAddTorus κ, ℂ)) (hH : IsCompact H) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ F ∈ H,
      ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F - F 0‖ < ε := by
  obtain ⟨t, _, ht, hcover⟩ := hH.finite_cover_balls (by positivity : 0 < ε/4)
  have hall : ∀ᶠ n in Filter.atTop, ∀ G ∈ ht.toFinset,
      ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) G - G 0‖ < ε/4 := by
    rw [Filter.eventually_all_finset]
    exact fun G _ => unit_torus_peak_kernel_evaluation_eventually_close G (ε/4) (by positivity)
  obtain ⟨n, hn⟩ := hall.exists
  refine ⟨n, ?_⟩
  intro F hF
  obtain ⟨G, hG⟩ := Set.mem_iUnion.mp (hcover hF)
  obtain ⟨hGt, hball⟩ := Set.mem_iUnion.mp hG
  have hd : ‖F-G‖ < ε/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hball
  have hGclose := hn G (ht.mem_toFinset.mpr hGt)
  have hbound : ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) F - F 0‖ ≤
      ‖F-G‖ + ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) G - G 0‖ + ‖F-G‖ := by
    calc
      _ = ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) (F-G) +
          (unitTorusKernelEvaluation (unitTorusPeakKernel κ n) G - G 0) - (F-G) 0‖ := by
        rw [unit_torus_kernel_evaluation_sub, ContinuousMap.sub_apply]
        congr 1
        ring
      _ ≤ ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) (F-G)‖ +
          ‖unitTorusKernelEvaluation (unitTorusPeakKernel κ n) G - G 0‖ + ‖(F-G) 0‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add
        (add_le_add (unit_torus_peak_kernel_evaluation_bound n (F-G)) le_rfl)
        ((F-G).norm_coe_le_norm 0)
  linarith only [hd, hGclose, hbound, hε]

end Hindman168
