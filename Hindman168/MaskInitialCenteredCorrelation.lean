import Hindman168.MaskEndpointCenteredDecay

/-! Unconditional initial centered tail-mask correlation decay. The actual
empty-mask endpoint condition is proved using the original additive source;
no endpoint-decay hypothesis remains in these statements. -/

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
theorem maskInitialCentered_uniform_zero (t : Fin (Fintype.card (LargeColumnSubset m))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ D : MaskStageCorrelationInput (maskSourceSupport m t) (maskSourceSupport_card m t)
        gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D
        (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w) →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| ≤ ε := by
  apply maskFiniteElimination_uniform_centered (maskSourceSupport m t) (maskSourceSupport_card m t)
    gap a ha C hC hgap htail
    (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t))
  intro η hη
  filter_upwards [maskTerminalCentered_uniform_zero gap a ha C hC J hJ hgap htail t η hη] with w hw
  intro E hE
  exact (hw E hE).le

include ha hC hJ hgap htail in
theorem maskInitialCentered_all_supports_uniform_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ D : MaskStageCorrelationInput (maskSourceSupport m t) (maskSourceSupport_card m t)
        gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D
        (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w) →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D| ≤ ε := by
  intro ε hε
  apply eventually_all.mpr
  intro t
  exact maskInitialCentered_uniform_zero gap a ha C hC J hJ hgap htail t ε hε

end Hindman168
