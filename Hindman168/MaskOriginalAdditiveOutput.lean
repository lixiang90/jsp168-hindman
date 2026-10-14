import Hindman168.MaskOriginalWeightedReplacement

/-! Full actual additive output after replacing the retained factor.
The coefficient depends only on m and the actual composed error tends
to zero. The source cube and original unshifted correlation are retained. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskRetainedMeanCap (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (maskRowCountBound m * 2 ^ maskRowCountBound m)

theorem maskRetainedMeanCap_ge_one (m : ℕ) : 1 ≤ maskRetainedMeanCap m :=
  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem retainedMeanConstant_nonneg (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    0 ≤ MaskRootOriginalSampling.retainedMeanConstant m gap t := Nat.cast_nonneg _

theorem retainedMeanConstant_le_cap (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    MaskRootOriginalSampling.retainedMeanConstant m gap t ≤ maskRetainedMeanCap m := by
  let d := MaskRootOriginalSampling.rootMomentDimension m gap t
  have hd : d ≤ maskRowCountBound m := maskGenerated_additive_dimension_le m gap t
  have hp : 2 ^ (d - 1) ≤ 2 ^ maskRowCountBound m :=
    Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.sub_le d 1).trans hd)
  have ht : d * 2 ^ (d - 1) ≤ maskRowCountBound m * 2 ^ maskRowCountBound m :=
    Nat.mul_le_mul hd hp
  unfold MaskRootOriginalSampling.retainedMeanConstant maskRetainedMeanCap
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht

noncomputable def maskAdditiveOutputBound (m : ℕ) : ℝ :=
  maskAdditiveRecurrenceBound m * maskRetainedMeanCap m

theorem maskAdditiveOutputBound_ge_one (m : ℕ) : 1 ≤ maskAdditiveOutputBound m := by
  have hD := maskAdditiveRecurrenceBound_ge_one m
  calc
    1 ≤ maskAdditiveRecurrenceBound m := hD
    _ = maskAdditiveRecurrenceBound m * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (maskRetainedMeanCap_ge_one m) (by linarith)

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

theorem source_unshifted_additive_output
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1)
    (hF : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
      maskAdditiveOutputBound m * |targetCubeAverage gap a ha C hC t J hJ hgap F w| + e w := by
  obtain ⟨e, he, hb⟩ := source_unshifted_smoothed_recurrence gap a ha C hC t J hJ hgap htail label F hroot hF
  let c := MaskRootOriginalSampling.retainedMeanConstant m gap t
  let δ : ℕ → ℝ := fun w => |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
    c * targetCubeAverage gap a ha C hC t J hJ hgap F w|
  have hc : 0 ≤ c := retainedMeanConstant_nonneg m gap t
  have hD : 0 ≤ maskAdditiveRecurrenceBound m := (by norm_num : (0 : ℝ) ≤ 1).trans
    (maskAdditiveRecurrenceBound_ge_one m)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [abs_zero] using
      (source_smoothed_replacement_tendsto_zero gap a ha C hC t J hJ hgap htail label F hroot).abs
  refine ⟨fun w => e w + maskAdditiveRecurrenceBound m * δ w, ?_, ?_⟩
  · simpa only [mul_zero, add_zero] using he.add (hδ.const_mul (maskAdditiveRecurrenceBound m))
  · filter_upwards [hb] with w hw
    have ht : |smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w| ≤
        c * |targetCubeAverage gap a ha C hC t J hJ hgap F w| + δ w := by
      calc
        _ = |c * targetCubeAverage gap a ha C hC t J hJ hgap F w +
            (smoothedTerminalAverage gap a ha C hC t J hJ hgap label F w -
              c * targetCubeAverage gap a ha C hC t J hJ hgap F w)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hc]
    have hmul := mul_le_mul_of_nonneg_left ht hD
    have hcap : maskAdditiveRecurrenceBound m * c *
        |targetCubeAverage gap a ha C hC t J hJ hgap F w| ≤
        maskAdditiveOutputBound m * |targetCubeAverage gap a ha C hC t J hJ hgap F w| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (retainedMeanConstant_le_cap m gap t) hD) (abs_nonneg _)
    nlinarith

end MaskOriginalSampling
end Hindman168
