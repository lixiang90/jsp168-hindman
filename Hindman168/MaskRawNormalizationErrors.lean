import Hindman168.MaskOriginalFullMajorant
import Mathlib.Algebra.Order.Ring.Abs

/-! Input-independent normalization and power errors for actual raw source
correlations. Uniform constant majorant caps allow every fixed correlation
power to be transferred without changing the additive output coefficient. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))

noncomputable def rawNormalizationError (w : ℕ) : ℝ :=
  |event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) - 1| *
    (2 * (originalMajorantMeanConstant gap t + 1)) + |originalBadMajorantMass gap a C t label w|

noncomputable def rawNormalizationPowerError (k w : ℕ) : ℝ :=
  rawNormalizationError gap a C t label w * (k : ℝ) *
    (2 * (originalMajorantMeanConstant gap t + 1)) ^ (k - 1)

include ha hC hgap htail in
theorem rawNormalizationError_tendsto_zero :
    Tendsto (rawNormalizationError gap a C t label) atTop (𝓝 0) := by
  unfold rawNormalizationError
  have hp : Tendsto (fun w => |event (basePrimeMass gap t w)
      (maskGeneratedCopiedPrimeGood m gap t w) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((baseGoodPrimeMass_tendsto_one gap t).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs
  simpa only [zero_mul, abs_zero, add_zero] using
    (hp.mul_const (2 * (originalMajorantMeanConstant gap t + 1))).add
      (originalBadMajorantMass_tendsto_zero gap a ha C hC t label hgap htail).abs

include ha hC hgap htail in
theorem rawNormalizationPowerError_tendsto_zero (k : ℕ) :
    Tendsto (rawNormalizationPowerError gap a C t label k) atTop (𝓝 0) := by
  unfold rawNormalizationPowerError
  simpa only [zero_mul] using ((rawNormalizationError_tendsto_zero gap a ha C hC t hgap htail label).mul_const
    (k : ℝ)).mul_const ((2 * (originalMajorantMeanConstant gap t + 1)) ^ (k - 1))

include ha hC htail in
theorem source_raw_conditioned_difference_bound :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |rawCorrelation gap a C t (fun _ => F) w -
        unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ≤
          rawNormalizationError gap a C t label w := by
  filter_upwards [source_correlations_constant_caps gap a ha C hC t label J hJ hgap htail,
    rawCorrelation_decomposition_eventually gap a ha C hC t J hJ hgap,
    original_bad_contribution_bound gap a C hC t label] with w hc hd hb
  intro F hF
  rw [hd (fun _ => F)]
  have he : event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) *
      unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w +
      badCorrelation gap a C t (fun _ => F) w - unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w =
      (event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) - 1) *
      unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w + badCorrelation gap a C t (fun _ => F) w := by ring
  rw [he]
  calc
    _ ≤ |(event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) - 1) *
      unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| +
      |badCorrelation gap a C t (fun _ => F) w| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hc F hF).2 (abs_nonneg _))
        ((hb F hF).trans (le_abs_self _))

include ha hC htail in
theorem source_raw_conditioned_power_difference_bound (k : ℕ) :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |(|rawCorrelation gap a C t (fun _ => F) w| ^ k -
        |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ^ k)| ≤
          rawNormalizationPowerError gap a C t label k w := by
  filter_upwards [source_raw_conditioned_difference_bound gap a ha C hC t J hJ hgap htail label,
    source_correlations_constant_caps gap a ha C hC t label J hJ hgap htail] with w hd hc
  intro F hF
  have hK : 0 ≤ originalMajorantMeanConstant gap t := Nat.cast_nonneg _
  have hraw := (hc F hF).1
  have hcond := (hc F hF).2
  have hmax : max |rawCorrelation gap a C t (fun _ => F) w|
      |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ≤
      2 * (originalMajorantMeanConstant gap t + 1) := max_le (by linarith) hcond
  have hdiff := (abs_abs_sub_abs_le_abs_sub (rawCorrelation gap a C t (fun _ => F) w)
    (unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w)).trans (hd F hF)
  have hpow := abs_pow_sub_pow_le (|rawCorrelation gap a C t (fun _ => F) w|)
    (|unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w|) k
  simp only [abs_abs] at hpow
  unfold rawNormalizationPowerError
  calc
    _ ≤ |(|rawCorrelation gap a C t (fun _ => F) w| -
        |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w|)| * (k : ℝ) *
        max |rawCorrelation gap a C t (fun _ => F) w|
          |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ^ (k - 1) := hpow
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg _)
      · exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax _
      · positivity
      · unfold rawNormalizationError
        positivity

include ha hC htail in
theorem source_raw_conditioned_power_difference_uniform_zero (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |(|rawCorrelation gap a C t (fun _ => F) w| ^ k -
        |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ^ k)| < ε := by
  intro ε hε
  filter_upwards [source_raw_conditioned_power_difference_bound gap a ha C hC t J hJ hgap htail label k,
    (rawNormalizationPowerError_tendsto_zero gap a ha C hC t hgap htail label k).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro F hF
  exact (hb F hF).trans_lt he

end Hindman168.MaskOriginalSampling
