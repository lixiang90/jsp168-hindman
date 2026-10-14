import Hindman168.MaskUnrestrictedAdditiveOutput
import Hindman168.MaskGeneralAdditiveOutput
import Hindman168.MaskGeneralUnrestrictedTransfer

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

theorem source_unshifted_unrestricted_additive_output_majorized
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
      maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w| + e w := by
  obtain ⟨e, he, hb⟩ := source_unshifted_additive_output_majorized gap a ha C hC t J hJ hgap htail label F hroot hF
  let δ : ℕ → ℝ := fun w => |targetCubeAverage gap a ha C hC t J hJ hgap F w -
    targetUnrestrictedAverage gap C t J F w|
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, abs_zero] using
      (source_targetCube_unrestricted_transfer_weighted_tendsto_majorized
        gap a ha C hC t J hJ hgap htail label F hroot 0).abs
  have hA : 0 ≤ maskAdditiveOutputBound m :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maskAdditiveOutputBound_ge_one m)
  refine ⟨fun w => e w + maskAdditiveOutputBound m * δ w, ?_, ?_⟩
  · simpa only [mul_zero, add_zero] using he.add (hδ.const_mul (maskAdditiveOutputBound m))
  · filter_upwards [hb] with w hw
    have ht : |targetCubeAverage gap a ha C hC t J hJ hgap F w| ≤
        |targetUnrestrictedAverage gap C t J F w| + δ w := by
      calc
        _ = |targetUnrestrictedAverage gap C t J F w +
            (targetCubeAverage gap a ha C hC t J hJ hgap F w - targetUnrestrictedAverage gap C t J F w)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    have hm := mul_le_mul_of_nonneg_left ht hA
    nlinarith

end Hindman168.MaskOriginalSampling
