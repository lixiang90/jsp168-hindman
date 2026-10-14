import Hindman168.MaskTargetProgressionLaw

/-! Transfer the actual cube average to the actual progression comparison.
The full original averaging law retains its finite coefficients, including
the prime-dependent quotient direction law. The derived error is rapidly small. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

include ha hC hJ in
theorem source_targetProgression_transfer_bound
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    ∀ᶠ w in atTop, |targetCubeAverage gap a ha C hC t J hJ hgap F w -
      targetProgressionAverage gap a C t J F w| ≤ targetRootTestErrorCap gap C t w := by
  filter_upwards [source_targetCube_uniform_anchor_comparison gap a ha C hC t hgap htail label F hroot J,
    rootPrimeMass_probability_eventually gap t, rootRestMass_probability_eventually gap C hC t,
    directionPairMass_probability_eventually gap t J hJ] with w hb hp hr hd
  rw [targetCubeAverage_eq_targetAnchorAverage]
  unfold targetAnchorAverage targetProgressionAverage
  calc
    _ ≤ total (rootPrimeMass gap t w) * targetRootTestErrorCap gap C t w := by
      apply expectation_difference_support_bound _ hp.1
      intro x hx
      have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
      calc
        _ ≤ total (MaskRootOriginalSampling.directionPairMass gap t J w x) * targetRootTestErrorCap gap C t w := by
          apply expectation_difference_support_bound _ (hd x hxG).1
          intro v hv
          calc
            _ ≤ total (rootRestMass gap C t w) * targetRootTestErrorCap gap C t w :=
              expectation_difference_support_bound _ hr.1 _ _ _ (fun rest hrest => hb x hxG rest v hrest hv)
            _ = _ := by rw [hr.2, one_mul]
        _ = _ := by rw [(hd x hxG).2, one_mul]
    _ = _ := by rw [hp.2, one_mul]

include ha hC hJ in
theorem source_targetProgression_transfer_rapid
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => targetCubeAverage gap a ha C hC t J hJ hgap F w - targetProgressionAverage gap a C t J F w) := by
  apply (targetRootTestErrorCap_rapid gap C hC t hgap).of_abs_le
  filter_upwards [source_targetProgression_transfer_bound gap a ha C hC t J hJ hgap htail label F hroot] with w hw
  exact hw.trans (le_abs_self _)

include ha hC hJ in
theorem source_targetProgression_transfer_weighted_tendsto
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (targetCubeAverage gap a ha C hC t J hJ hgap F w - targetProgressionAverage gap a C t J F w)) atTop (𝓝 0) := by
  apply (isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using
    ((source_targetProgression_transfer_rapid gap a ha C hC t J hJ hgap htail label F hroot).mul_power
      (Eventually.of_forall (fun w => by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
          ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0

end Hindman168.MaskOriginalSampling
