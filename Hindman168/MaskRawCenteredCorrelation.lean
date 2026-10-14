import Hindman168.MaskRawCorrelationTransfer
import Hindman168.MaskCenteredCorrelationUniform

/-! Centered source cancellation under the actual unconditioned prime and
harmonic laws. All rows are majorized on the original prime-pool support;
the centered-root identity is needed only on good tuples. Uniformity holds
for all per-stage inputs with the fixed actual source parameters. -/

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

include ha hC J hJ hgap htail in
theorem source_rawCorrelation_tendsto_zero
    (F : ℕ → MaskCenteredInput gap t)
    (hroot : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      F w x none = targetRootCenteredMask gap C t label w)
    (hF : ∀ᶠ w in atTop, ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
      |F w x base y| ≤ rowMajorant gap C t label w base y) :
    Tendsto (rawCorrelation gap a C t F) atTop (𝓝 0) := by
  have hoff : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |F w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y :=
    hF.mono (fun _ hw x hx k y => hw x hx.1 _ y)
  exact rawCorrelation_tendsto_zero_of_conditioned gap a ha C hC t J hJ hgap htail label F hF
    (source_unshiftedCorrelation_tendsto_zero gap a ha C hC t J hJ hgap htail label F hroot hoff)

def rawCenteredSourceAdmissible (w : ℕ) (G : MaskCenteredInput gap t) : Prop :=
  centeredSourceAdmissible gap C t label w G ∧
    ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
      |G x base y| ≤ rowMajorant gap C t label w base y

include hC htail in
theorem centeredSourceDefault_eventually_raw_admissible :
    ∀ᶠ w in atTop, rawCenteredSourceAdmissible gap C t label w
      (centeredSourceDefault gap C t label w) := by
  filter_upwards [centeredSourceDefault_eventually_admissible gap C hC t label,
    masks_eventually_bounded gap C hC t htail label,
    rowMajorant_eventually_nonneg gap C hC t label] with w hc hm hn
  refine ⟨hc, ?_⟩
  intro x _ base y
  by_cases hb : base = none
  · subst base
    simp only [centeredSourceDefault]
    change |integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1| ≤
        1 + integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y
    exact abs_le.mpr ⟨by linarith [(hm none y).1], by linarith⟩
  · simpa only [centeredSourceDefault, if_neg hb, abs_zero] using hn base y

include ha hC J hJ hgap htail in
theorem source_rawCorrelation_uniform_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ G : MaskCenteredInput gap t,
      rawCenteredSourceAdmissible gap C t label w G →
      |rawCorrelation gap a C t (fun _ => G) w| < ε := by
  apply uniform_zero_of_admissible_sequences
    (rawCenteredSourceAdmissible gap C t label)
    (fun w G => rawCorrelation gap a C t (fun _ => G) w)
    (centeredSourceDefault gap C t label)
    (centeredSourceDefault_eventually_raw_admissible gap C hC t htail label)
  intro G hG
  have hr : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      G w x none = targetRootCenteredMask gap C t label w :=
    hG.mono (fun _ hw x hx => (hw.1 x hx).1)
  have hb : ∀ᶠ w in atTop, ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
      |G w x base y| ≤ rowMajorant gap C t label w base y := hG.mono (fun _ hw => hw.2)
  have ht := source_rawCorrelation_tendsto_zero gap a ha C hC t J hJ hgap htail label G hr hb
  have he : (fun w => rawCorrelation gap a C t (fun _ => G w) w) = rawCorrelation gap a C t G := by
    funext w
    rfl
  exact he.symm ▸ ht

end Hindman168.MaskOriginalSampling
