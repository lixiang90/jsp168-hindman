import Hindman168.MaskCenteredCorrelationLimit
import Hindman168.UniformAdmissibleInputLimit

/-! Qualitative uniform vanishing over every allowed original source input.
The admissible default uses the actual centered root and zero elsewhere;
no compactness, maximum or assumed rate is needed. -/

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

abbrev MaskCenteredInput :=
  (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ

def centeredSourceAdmissible (w : ℕ) (G : MaskCenteredInput gap t) : Prop :=
  ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
    G x none = targetRootCenteredMask gap C t label w ∧
      ∀ k y, |G x (some (additiveRowAssigned _ k)) y| ≤
        rowMajorant gap C t label w (some (additiveRowAssigned _ k)) y

noncomputable def centeredSourceDefault (w : ℕ) : MaskCenteredInput gap t :=
  fun _ base y => if base = none then targetRootCenteredMask gap C t label w y else 0

include hC in
theorem centeredSourceDefault_eventually_admissible :
    ∀ᶠ w in atTop, centeredSourceAdmissible gap C t label w (centeredSourceDefault gap C t label w) := by
  filter_upwards [rowMajorant_eventually_nonneg gap C hC t label] with w hw
  intro x _
  constructor
  · funext y
    simp [centeredSourceDefault]
  · intro k y
    simpa only [centeredSourceDefault, Option.some_ne_none, if_false, abs_zero] using hw (some (additiveRowAssigned _ k)) y

include htail in
theorem source_unshiftedCorrelation_uniform_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ G : MaskCenteredInput gap t,
      centeredSourceAdmissible gap C t label w G →
      |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G) w| < ε := by
  apply uniform_zero_of_admissible_sequences
    (centeredSourceAdmissible gap C t label)
    (fun w G => unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G) w)
    (centeredSourceDefault gap C t label) (centeredSourceDefault_eventually_admissible gap C hC t label)
  intro G hG
  have hr : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      G w x none = fun y => integerDivisorMask (tailMass (primorial w)
        ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) (label w none))) y - 1 :=
    hG.mono (fun _ hw x hx => (hw x hx).1)
  have hb : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ k y,
      |G w x (some (additiveRowAssigned _ k)) y| ≤ rowMajorant gap C t label w
        (some (additiveRowAssigned _ k)) y := hG.mono (fun _ hw x hx => (hw x hx).2)
  have ht := source_unshiftedCorrelation_tendsto_zero gap a ha C hC t J hJ hgap htail label G hr hb
  have he : (fun w => unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => G w) w) =
      unshiftedCorrelation gap a ha C hC t J hJ hgap G := by
    funext w
    rfl
  exact he.symm ▸ ht

end Hindman168.MaskOriginalSampling
