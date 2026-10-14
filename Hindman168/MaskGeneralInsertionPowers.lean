import Hindman168.MaskOriginalInsertionPowers
import Hindman168.MaskGeneralInsertionLimit

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

theorem source_insertion_power_error_rapid_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (insertionPowerError gap a ha C hC t J hJ hgap F) := by
  have hi := source_insertion_difference_rapid_majorized gap a ha C hC t J hJ hgap htail label F hroot hF
  have he : RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => unshiftedCorrelation gap a ha C hC t J hJ hgap F w -
        insertedCorrelation gap a ha C hC t J hJ hgap F w) :=
    hi.of_abs_le (Eventually.of_forall (fun w => le_of_eq (abs_sub_comm _ _)))
  have hb := correlations_eventually_bounded gap a ha C hC t J hJ hgap F 2
    (source_tests_eventually_sup_bound_majorized gap C hC t htail label F hroot hF)
  exact he.abs_power_difference (Eventually.of_forall (fun w => by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))
    (2 * Fintype.card (MaskOriginalBaseRow m gap t))
    (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target))
    (hb.mono (fun _ hw => hw.1)) (hb.mono (fun _ hw => hw.2))

theorem source_insertion_power_error_weighted_tendsto_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      |insertionPowerError gap a ha C hC t J hJ hgap F w|) atTop (𝓝 0) := by
  have he := source_insertion_power_error_rapid_majorized gap a ha C hC t J hJ hgap htail label F hroot hF
  have ht : Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      insertionPowerError gap a ha C hC t J hJ hgap F w) atTop (𝓝 0) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mp
    simpa only [pow_zero, inv_one] using
      (he.mul_power (Eventually.of_forall (fun w => by
        exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
          ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0
  have hv (w : ℕ) :
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q| =
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q :=
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) q)
  simpa only [abs_zero, abs_mul, hv] using ht.abs

theorem source_unshifted_recurrence_majorized
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
      maskAdditiveRecurrenceBound m * |terminalAverage gap a ha C hC t J hJ hgap label F w| + e w := by
  refine ⟨fun w => |insertionPowerError gap a ha C hC t J hJ hgap F w|, ?_, ?_⟩
  · simpa only [pow_zero, one_mul] using
      source_insertion_power_error_weighted_tendsto_majorized gap a ha C hC t J hJ hgap htail label F hroot hF 0
  · filter_upwards [inserted_correlation_power_bound gap a ha C hC t J hJ hgap htail label F hF] with w hw
    have he := le_abs_self (insertionPowerError gap a ha C hC t J hJ hgap F w)
    change |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
      |insertedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      |insertionPowerError gap a ha C hC t J hJ hgap F w| at he
    linarith

end Hindman168.MaskOriginalSampling
