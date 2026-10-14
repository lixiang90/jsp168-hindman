import Hindman168.MaskTargetCubeDecay
import Hindman168.MaskUnrestrictedAdditiveOutput

/-! The original unshifted correlation vanishes when its actual target is
the centered divisor mask and the other rows satisfy their actual source
majorants. This is a source application, not the full arbitrary-target
correlation principle or the finite sums/products theorem. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
  (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
  (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
    F w x none = fun y => integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
  (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
    |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
      (some (additiveRowAssigned _ k)) y)

include htail label hroot hF in
theorem source_unshiftedCorrelation_power_tendsto_zero :
    Tendsto (fun w => |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
      (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)))
      atTop (𝓝 0) := by
  obtain ⟨e, he, hb⟩ := source_unshifted_unrestricted_additive_output
    gap a ha C hC t J hJ hgap htail label F hroot hF
  have hcube := source_targetUnrestrictedAverage_tendsto_zero gap C hC t J hJ hgap htail label F hroot
  have hupper : Tendsto (fun w => maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w| + e w)
      atTop (𝓝 0) := by
    simpa only [abs_zero, mul_zero, add_zero] using (hcube.abs.const_mul (maskAdditiveOutputBound m)).add he
  exact squeeze_zero' (Eventually.of_forall (fun _ => pow_nonneg (abs_nonneg _) _)) hb hupper

include htail label hroot hF in
theorem source_unshiftedCorrelation_abs_tendsto_zero :
    Tendsto (fun w => |unshiftedCorrelation gap a ha C hC t J hJ hgap F w|) atTop (𝓝 0) := by
  have hp := source_unshiftedCorrelation_power_tendsto_zero gap a ha C hC t J hJ hgap htail label F hroot hF
  let k := 2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun _ => hb.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [hp.eventually (eventually_lt_nhds (pow_pos hε k))] with w hw
    by_contra! h
    exact (not_lt_of_ge (pow_le_pow_left₀ hε.le h k)) hw

include htail label hroot hF in
theorem source_unshiftedCorrelation_tendsto_zero :
    Tendsto (unshiftedCorrelation gap a ha C hC t J hJ hgap F) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    source_unshiftedCorrelation_abs_tendsto_zero gap a ha C hC t J hJ hgap htail label F hroot hF

end Hindman168.MaskOriginalSampling
