import Hindman168.MaskOriginalInsertionLimit
import Hindman168.MaskGeneralFunctionBounds

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

theorem source_insertion_difference_rapid_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w) :=
  insertion_difference_rapid gap a ha C hC t J hJ hgap F 2
    (source_tests_eventually_sup_bound_majorized gap C hC t htail label F hroot hF)

theorem source_insertion_weighted_tendsto_zero_majorized
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      ∀ y, |F w x none y| ≤ rowMajorant gap C t label w none y)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) (q : ℕ) :
    Tendsto (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (insertedCorrelation gap a ha C hC t J hJ hgap F w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap F w)) atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using
    ((source_insertion_difference_rapid_majorized gap a ha C hC t J hJ hgap htail label F hroot hF).mul_power
      (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q) 0

end Hindman168.MaskOriginalSampling
