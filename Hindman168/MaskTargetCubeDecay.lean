import Hindman168.MaskTargetPredictionIdentification

/-! Actual centered-root cube decay. The raw prediction cube limit is
normalized only by the proved good-event mass tending to one, then the
original source cube is recovered through its proved rapid transfer. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include hC hJ hgap in
theorem targetCenteredUnrestrictedAverage_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    Tendsto (targetCenteredUnrestrictedAverage gap C t J label) atTop (𝓝 0) := by
  have hraw := targetPredictionAverage_tendsto_zero gap C hC t J hJ hgap htail label
  have hmass := maskGeneratedCopiedGood_event_tendsto_one m gap t
  have hdiv := hraw.div hmass (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [zero_div] using hdiv.congr' (Eventually.of_forall (fun w =>
    (targetCenteredUnrestrictedAverage_eq_prediction_normalized gap C hC t J label w).symm))

include hC hJ hgap in
theorem source_targetUnrestrictedAverage_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    Tendsto (targetUnrestrictedAverage gap C t J F) atTop (𝓝 0) :=
  (targetCenteredUnrestrictedAverage_tendsto_zero gap C hC t J hJ hgap htail label).congr'
    ((source_targetUnrestrictedAverage_eq_centered gap C t J label F hroot).mono (fun _ hw => hw.symm))

theorem source_targetCubeAverage_tendsto_zero
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    Tendsto (targetCubeAverage gap a ha C hC t J hJ hgap F) atTop (𝓝 0) := by
  have hdelta := source_targetCube_unrestricted_transfer_weighted_tendsto
    gap a ha C hC t J hJ hgap htail label F hroot 0
  have hcube := source_targetUnrestrictedAverage_tendsto_zero gap C hC t J hJ hgap htail label F hroot
  simpa only [pow_zero, one_mul, sub_add_cancel, add_zero] using hdelta.add hcube

end Hindman168.MaskOriginalSampling
