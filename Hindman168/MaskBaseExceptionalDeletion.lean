import Hindman168.MaskBaseRestrictedMajorant
import Hindman168.MaskCopiedNormalizedMoments

/-! The whole original bad-prime event has vanishing weighted base-row
majorant mass. Its probability limit is derived from the actual generated
good-event law, rather than supplied as an application premise. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

theorem basePrime_probability (w : ℕ) :
    (∀ x, 0 ≤ basePrimeMass gap t w x) ∧ total (basePrimeMass gap t w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact ⟨hF.prime_slots_nonneg w (fun _ => (gap w).val),
    hF.prime_slots_total w (fun _ => (gap w).val)⟩

theorem baseGoodPrimeMass_tendsto_one :
    Tendsto (fun w => event (basePrimeMass gap t w)
      (maskGeneratedCopiedPrimeGood m gap t w)) atTop (𝓝 1) :=
  maskGeneratedCopiedGood_event_tendsto_one m gap t

theorem baseBadPrimeMass_tendsto_zero :
    Tendsto (fun w => event (basePrimeMass gap t w)
      (fun x => ¬ maskGeneratedCopiedPrimeGood m gap t w x)) atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (baseGoodPrimeMass_tendsto_one gap t)
  simpa only [event_complement, (basePrime_probability gap t _).2, sub_self] using ht

include ha hC in
theorem baseBadMajorant_tendsto_zero {q : ℕ}
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → Fin q → Fin (m + 1))
    (row : ℕ → Fin q → Fin (maskGeneratedRowDataFamily m gap t).rowCount)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w)) (U : Finset (Fin q)) :
    Tendsto (baseRestrictedMajorant gap a C t label row
      (fun w x => ¬ maskGeneratedCopiedPrimeGood m gap t w x) U) atTop (𝓝 0) := by
  exact baseRestrictedMajorant_tendsto_zero gap a ha C hC t hgap htail label row hrow
    _ (baseBadPrimeMass_tendsto_zero gap t) U

end Hindman168.MaskOriginalSampling
