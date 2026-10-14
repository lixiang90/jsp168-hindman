import Hindman168.MaskOriginalWeightedReplacement
import Hindman168.MaskGeneralNativeReplacement

/-! General target-row version under |F_root| ≤ 1 + ν.
The original sampling laws and retained majorants remain unchanged.
All error estimates are proved from the source parameters. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

theorem source_smoothed_replacement_tendsto_zero_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y) :
    Tendsto (fun w => smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
      MaskRootOriginalSampling.retainedMeanConstant m gap t *
        targetCubeAverage gap a ha C hC t J hJ hgap F w) atTop (𝓝 0) := by
  have ht := MaskRootOriginalSampling.source_native_terminal_replacement_tendsto_zero_majorized
    gap a ha C hC t J hJ hgap htail label F hroot
  exact ht.congr (fun w => by rw [smoothedTerminalAverage_eq_native, targetCubeAverage_eq_native])

end Hindman168.MaskOriginalSampling
