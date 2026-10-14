import Hindman168.MaskOriginalSmoothedTerminal
import Hindman168.MaskGeneralRetainedRootSmoothing

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

theorem source_smoothed_terminal_difference_rapid_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w) := by
  apply (source_terminal_root_smoothing_rapid_majorized gap a ha C hC t J hJ hgap htail label F hroot hF).of_abs_le
  filter_upwards [rootSmoothedAverage_terminal_eq_eventually gap a ha C hC t J hJ hgap label F] with w hw
  rw [hw]

theorem source_smoothed_terminal_weighted_tendsto_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w|) atTop (𝓝 0) := by
  have ht : Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
        terminalAverage gap a ha C hC t J hJ hgap label F w)) atTop (𝓝 0) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using
      ((source_smoothed_terminal_difference_rapid_majorized gap a ha C hC t J hJ hgap htail label F hroot hF).mul_power
        (Eventually.of_forall (fun w => by
          exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
            ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0
  have hv (w : ℕ) : |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q| =
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) q)
  simpa only [abs_zero, abs_mul, hv] using ht.abs

theorem source_unshifted_smoothed_recurrence_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      maskAdditiveRecurrenceBound m * |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w| + e w := by
  obtain ⟨e, he, hb⟩ := source_unshifted_recurrence_majorized gap a ha C hC t J hJ hgap htail label F hroot hF
  let δ : ℕ → ℝ := fun w => |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
    terminalAverage gap a ha C hC t J hJ hgap label F w|
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using source_smoothed_terminal_weighted_tendsto_majorized
      gap a ha C hC t J hJ hgap htail label F hroot hF 0
  refine ⟨fun w => e w + maskAdditiveRecurrenceBound m * δ w, ?_, ?_⟩
  · simpa only [mul_zero, add_zero] using he.add (hδ.const_mul (maskAdditiveRecurrenceBound m))
  · filter_upwards [hb] with w hw
    have hD : 0 ≤ maskAdditiveRecurrenceBound m := le_trans (by norm_num)
      (maskAdditiveRecurrenceBound_ge_one m)
    have hd := abs_abs_sub_abs_le_abs_sub
      (smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w)
      (terminalAverage gap a ha C hC t J hJ hgap label F w)
    have hh := neg_le_of_abs_le hd
    have hnorm : |terminalAverage gap a ha C hC t J hJ hgap label F w| ≤
        |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w| + δ w := by
      dsimp only [δ]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hnorm hD
    linarith

end Hindman168.MaskOriginalSampling
