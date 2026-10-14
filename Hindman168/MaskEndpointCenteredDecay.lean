import Hindman168.MaskEndpointTerminalTransfer

/-! Actual centered empty-mask endpoint decay. The source admissibility
and exact average are derived from the genuine terminal input, so the
previous explicit endpoint hypothesis is discharged for the centered
original tail divisor mask. -/

namespace Hindman168

open Filter
open scoped Topology Classical
open MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include ha hC hJ hgap htail in
theorem maskTerminalCentered_uniform_zero (t : Fin (Fintype.card (LargeColumnSubset m))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ D : MaskIndexedTerminalInput gap C t w,
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D
        (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w) →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| < ε := by
  intro ε hε
  filter_upwards [source_rawCorrelation_uniform_zero gap a ha C hC t J hJ hgap htail
    (maskEndpointLabel gap t) ε hε] with w hw
  intro D hD
  have he := hw (maskEndpointSource gap C t (maskEndpointFromTerminal gap C t D))
    (maskEndpointFromTerminal_centered_admissible gap C t D hD)
  rw [← maskEndpointFromTerminal_rawCorrelation gap a C t D] at he
  exact he

include ha hC hJ hgap htail in
theorem maskTerminalCentered_all_supports_uniform_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ D : MaskIndexedTerminalInput gap C t w,
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D
        (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w) →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| < ε := by
  intro ε hε
  apply eventually_all.mpr
  intro t
  exact maskTerminalCentered_uniform_zero gap a ha C hC J hJ hgap htail t ε hε

end Hindman168
