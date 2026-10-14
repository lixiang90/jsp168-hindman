import Hindman168.MaskGeneralUnrestrictedAdditiveOutput
import Hindman168.MaskCenteredCorrelationUniform

/-! Uniform general-target correlation inequality. Every original row is
bounded by its actual one-plus-divisor-mask majorant. The repeated target
cube remains on the right; no arbitrary-target cube decay is asserted. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))

def majorizedSourceAdmissible (w : ℕ) (G : MaskCenteredInput gap t) : Prop :=
  ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ base y,
    |G x base y| ≤ rowMajorant gap C t label w base y

include hC in
theorem zeroSource_eventually_majorized :
    ∀ᶠ w in atTop, majorizedSourceAdmissible gap C t label w (fun _ _ _ => 0) := by
  filter_upwards [rowMajorant_eventually_nonneg gap C hC t label] with w hw
  intro x _ base y
  simpa only [abs_zero] using hw base y

include htail in
theorem source_general_additive_excess_tendsto
    (F : ℕ → MaskCenteredInput gap t)
    (hF : ∀ᶠ w in atTop, majorizedSourceAdmissible gap C t label w (F w)) :
    Tendsto (fun w => max
      (|unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J F w|) 0)
      atTop (𝓝 0) := by
  have hr : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ y,
      |F w x none y| ≤ rowMajorant gap C t label w none y :=
    hF.mono (fun _ hw x hx y => hw x hx none y)
  have hb : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤
        rowMajorant gap C t label w (some (additiveRowAssigned _ k)) y :=
    hF.mono (fun _ hw x hx k y => hw x hx _ y)
  obtain ⟨e, he, hbound⟩ := source_unshifted_unrestricted_additive_output_majorized
    gap a ha C hC t J hJ hgap htail label F hr hb
  have hmax : Tendsto (fun w => max (e w) 0) atTop (𝓝 0) := by
    simpa only [max_self] using he.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply squeeze_zero' (Eventually.of_forall (fun _ => le_max_right _ _)) _ hmax
  filter_upwards [hbound] with w hw
  exact max_le_max_right 0 (by linarith)

include htail in
theorem source_general_additive_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ G : MaskCenteredInput gap t,
      majorizedSourceAdmissible gap C t label w G →
      |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G) w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) ≤
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w| + ε := by
  have huniform := uniform_zero_of_admissible_sequences
    (majorizedSourceAdmissible gap C t label)
    (fun w G => max
      (|unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G) w| ^
        (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
        maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w|) 0)
    (fun _ => (fun _ _ _ => (0 : ℝ))) (zeroSource_eventually_majorized gap C hC t label)
    (by
      intro F hF
      have ht := source_general_additive_excess_tendsto gap a ha C hC t J hJ hgap htail label F hF
      have he : (fun w => max
          (|unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F w) w| ^
            (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
            maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => F w) w|) 0) =
          (fun w => max
          (|unshiftedCorrelation gap a ha C hC t J hJ hgap F w| ^
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
    (|unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G) w| ^
      (2 ^ Fintype.card (PolynomialRowFamily.OffTargetRow (maskGeneratedRowDataFamily m gap t).target)) -
      maskAdditiveOutputBound m * |targetUnrestrictedAverage gap C t J (fun _ => G) w|) (0 : ℝ)).trans
      (le_abs_self _)
  linarith

include htail in
theorem source_general_cube_transfer_uniform (q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ G : MaskCenteredInput gap t,
      majorizedSourceAdmissible gap C t label w G →
      |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
        (targetCubeAverage gap a ha C hC t J hJ hgap (fun _ => G) w -
          targetUnrestrictedAverage gap C t J (fun _ => G) w)| < ε := by
  apply uniform_zero_of_admissible_sequences
    (majorizedSourceAdmissible gap C t label)
    (fun w G => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (targetCubeAverage gap a ha C hC t J hJ hgap (fun _ => G) w -
        targetUnrestrictedAverage gap C t J (fun _ => G) w))
    (fun _ => (fun _ _ _ => (0 : ℝ))) (zeroSource_eventually_majorized gap C hC t label)
  intro F hF
  have hr : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ y,
      |F w x none y| ≤ rowMajorant gap C t label w none y :=
    hF.mono (fun _ hw x hx y => hw x hx none y)
  have ht := source_targetCube_unrestricted_transfer_weighted_tendsto_majorized
    gap a ha C hC t J hJ hgap htail label F hr q
  have he : (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (targetCubeAverage gap a ha C hC t J hJ hgap (fun _ => F w) w -
        targetUnrestrictedAverage gap C t J (fun _ => F w) w)) =
      (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q *
      (targetCubeAverage gap a ha C hC t J hJ hgap F w -
        targetUnrestrictedAverage gap C t J F w)) := by
    funext w
    rfl
  exact he.symm ▸ ht

end Hindman168.MaskOriginalSampling
