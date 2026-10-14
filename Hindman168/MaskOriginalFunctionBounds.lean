import Hindman168.MaskOriginalTranslationError
import Hindman168.PredictionDivisorSupBounds

/-! The original tail probability laws give pointwise polynomial bounds
for all source tests, including the centered distinguished row. No sup
bound or rapidly-small insertion conclusion is assumed in this application. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem masks_eventually_bounded (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ base y,
      0 ≤ integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w base))) y ∧
      integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w base))) y ≤
          (maskGeneratedMaster m gap).auxiliary w (gap w).val := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact hF.prediction_masks_eventually_bounded C hC label
    (fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val)
    (htail.mono (fun w hw base => hF.chain_tail_budget_at_gap (C w) w
      (label w base) (gap w).val (hw (label w base))))

include hC htail in
theorem rowMajorant_eventually_le (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ base y,
      rowMajorant gap C t label w base y ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ 2 := by
  filter_upwards [masks_eventually_bounded gap C hC t htail label] with w hw
  intro base y
  have hv : (2 : ℝ) ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val := by
    exact_mod_cast (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
  unfold rowMajorant
  nlinarith [(hw base y).2]

include hC htail in
theorem source_tests_eventually_sup_bound
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ base y,
      |F w x base y| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ 2 := by
  filter_upwards [masks_eventually_bounded gap C hC t htail label,
    rowMajorant_eventually_le gap C hC t htail label, hroot, hF] with w hm hb hr hf
  intro x hx base y
  cases base with
  | none =>
    have he := congrFun (hr x hx) y
    rw [he]
    have ht := abs_sub (integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y) (1 : ℝ)
    rw [abs_of_nonneg (hm none y).1] at ht
    norm_num only [abs_one] at ht
    have hh : |integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1| ≤
        rowMajorant gap C t label w none y := by
      simpa only [rowMajorant, add_comm] using ht
    exact hh.trans (hb none y)
  | some row =>
    obtain ⟨k, rfl⟩ := additiveRowAssigned_surjective _ row
    exact (hf x hx k y).trans (hb _ y)

end Hindman168.MaskOriginalSampling
