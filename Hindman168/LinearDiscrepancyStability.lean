import Hindman168.CompactLipschitzApproximation

/-! Uniform approximation errors for a complex linear discrepancy of norm at most two. -/

namespace Hindman168

theorem linear_discrepancy_approximation_error (X : Type*) [MetricSpace X] [CompactSpace X]
    (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ F, ‖Λ F‖ ≤ 2*‖F‖)
    (F G : C(X, ℂ)) (ε : ℝ) (hClose : ‖F-G‖ < ε) :
    ‖Λ F-Λ G‖ < 2*ε := by
  rw [← map_sub]
  exact (hΛ (F-G)).trans_lt (by linarith only [hClose])

theorem linear_discrepancy_approximant_detection (X : Type*) [MetricSpace X] [CompactSpace X]
    (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ F, ‖Λ F‖ ≤ 2*‖F‖)
    (F G : C(X, ℂ)) (ε δ : ℝ) (hClose : ‖F-G‖ < ε) (hLarge : δ ≤ ‖Λ F‖) :
    δ-2*ε < ‖Λ G‖ := by
  have hErr := linear_discrepancy_approximation_error X Λ hΛ F G ε hClose
  have hTri : ‖Λ F‖ ≤ ‖Λ F-Λ G‖+‖Λ G‖ := by
    simpa only [sub_add_cancel] using norm_add_le (Λ F-Λ G) (Λ G)
  linarith only [hErr,hTri,hLarge]

end Hindman168
