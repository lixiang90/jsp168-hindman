import Hindman168.MaskRawNormalizationErrors
import Hindman168.MaskGeneralCorrelationUniform

/-! The arbitrary-target additive source inequality under the original
unconditioned prime and harmonic laws. The same m-only output coefficient
and actual repeated target cube are retained, with a derived error. -/

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

def rawMajorizedSourceAdmissible (w : ℕ) (G : MaskCenteredInput gap t) : Prop :=
  ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
    |G x base y| ≤ rowMajorant gap C t label w base y

theorem rawMajorizedSourceAdmissible.good (w : ℕ) (G : MaskCenteredInput gap t)
    (hG : rawMajorizedSourceAdmissible gap C t label w G) :
    majorizedSourceAdmissible gap C t label w G :=
  fun x hx base y => hG x hx.1 base y

include hC in
theorem zeroSource_eventually_raw_majorized :
    ∀ᶠ w in atTop, rawMajorizedSourceAdmissible gap C t label w (fun _ _ _ => 0) := by
  filter_upwards [rowMajorant_eventually_nonneg gap C hC t label] with w hw
  intro x _ base y
  simpa only [abs_zero] using hw base y

include ha hC hJ hgap htail in
theorem source_raw_unrestricted_additive_output_majorized
    (F : ℕ → MaskCenteredInput gap t)
    (hF : ∀ᶠ w in atTop, rawMajorizedSourceAdmissible gap C t label w (F w)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      |rawCorrelation gap a C t F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w| + e w := by
  have hr : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ y,
      |F w x none y| ≤ rowMajorant gap C t label w none y :=
    hF.mono (fun _ hw x hx y => hw x hx.1 none y)
  have hoff : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y := hF.mono (fun _ hw x hx k y => hw x hx.1 _ y)
  obtain ⟨e, he, hb⟩ := source_unshifted_unrestricted_additive_output_majorized
    gap a ha C hC t J hJ hgap htail label F hr hoff
  let k := 2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)
  refine ⟨fun w => e w + rawNormalizationPowerError gap a C t label k w, ?_, ?_⟩
  · simpa only [add_zero] using he.add
      (rawNormalizationPowerError_tendsto_zero gap a ha C hC t hgap htail label k)
  · filter_upwards [hb, hF,
      source_raw_conditioned_power_difference_bound gap a ha C hC t J hJ hgap htail label k] with w hw hf hp
    have hd := hp (F w) hf
    have hh := (le_abs_self (|rawCorrelation gap a C t F w| ^ k -
      |unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^ k)).trans hd
    linarith

include ha hC hJ hgap htail in
theorem source_raw_general_additive_excess_tendsto
    (F : ℕ → MaskCenteredInput gap t)
    (hF : ∀ᶠ w in atTop, rawMajorizedSourceAdmissible gap C t label w (F w)) :
    Tendsto (fun w => max
      (|rawCorrelation gap a C t F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w|) 0)
      atTop (𝓝 0) := by
  obtain ⟨e, he, hb⟩ := source_raw_unrestricted_additive_output_majorized gap a ha C hC t J hJ hgap htail label F hF
  have hmax : Tendsto (fun w => max (e w) 0) atTop (𝓝 0) := by
    simpa only [max_self] using he.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply squeeze_zero' (Eventually.of_forall (fun _ => le_max_right _ _)) _ hmax
  filter_upwards [hb] with w hw
  exact max_le_max_right 0 (by linarith)

include ha hC hJ hgap htail in
theorem source_raw_general_additive_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ G : MaskCenteredInput gap t,
      rawMajorizedSourceAdmissible gap C t label w G →
      |rawCorrelation gap a C t (fun _ => G) w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w| + ε := by
  have huniform := uniform_zero_of_admissible_sequences
    (rawMajorizedSourceAdmissible gap C t label)
    (fun w G => max
      (|rawCorrelation gap a C t (fun _ => G) w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w|) 0)
    (fun _ => (fun _ _ _ => (0 : ℝ))) (zeroSource_eventually_raw_majorized gap C hC t label)
    (by
      intro F hF
      have ht := source_raw_general_additive_excess_tendsto gap a ha C hC t J hJ hgap htail label F hF
      have he : (fun w => max
          (|rawCorrelation gap a C t (fun _ => F w) w| ^
            (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
            maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => F w) w|) 0) =
          (fun w => max
          (|rawCorrelation gap a C t F w| ^
            (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
            maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w|) 0) := by
        funext w
        rfl
      exact he.symm ▸ ht)
  intro ε hε
  filter_upwards [huniform ε hε] with w hw
  intro G hG
  have hh := hw G hG
  have hm := (le_max_left
    (|rawCorrelation gap a C t (fun _ => G) w| ^
      (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
      maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w|) (0 : ℝ)).trans
      (le_abs_self _)
  linarith

end Hindman168.MaskOriginalSampling
