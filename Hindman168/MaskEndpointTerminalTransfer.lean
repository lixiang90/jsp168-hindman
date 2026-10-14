import Hindman168.MaskEndpointSourceRows

/-! Transfer the actual empty-mask terminal input to the indexed full
stage and its additive source. The endpoint centered root is exactly the
initial centered tail mask, with the proved original anchor retained. -/

namespace Hindman168

open scoped Classical
open MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))

noncomputable def maskInitialCenteredTarget (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card)
    (w : ℕ) (y : ℤ) : ℝ :=
  integerDivisorMask (maskStageRowDivisorMass S hS gap C 0 w (maskPrefixRowStage S hS 0).target) y - 1

abbrev MaskIndexedTerminalInput (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) :=
  MaskStageCorrelationInput (maskSourceSupport m t) (maskSourceSupport_card m t) gap C
    (allNonemptyColumnMasks m).length w ∅

variable (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def maskEndpointFromTerminal {w : ℕ} (D : MaskIndexedTerminalInput gap C t w) :
    MaskEndpointInput gap C t w :=
  maskRowStageInputTransport (maskSourceSupport m t) gap C
    (maskPrefixRowStage_full (maskSourceSupport m t) (maskSourceSupport_card m t))
    (maskStageInput_toRowStageInput (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D)

theorem maskEndpointFromTerminal_correlation {w : ℕ} (D : MaskIndexedTerminalInput gap C t w) :
    maskRowStageInputCorrelation (maskSourceSupport m t) gap a C (maskEndpointFromTerminal gap C t D) =
      maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D := by
  unfold maskEndpointFromTerminal
  rw [maskRowStageInputTransport_correlation]
  rfl

theorem maskEndpointFromTerminal_target {w : ℕ} (D : MaskIndexedTerminalInput gap C t w)
    (g : ℤ → ℝ) (hD : maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D g) :
    maskRowStageInputHasTarget (maskSourceSupport m t) gap C (maskEndpointFromTerminal gap C t D) g := by
  exact (maskRowStageInputTransport_hasTarget (maskSourceSupport m t) gap C
    (maskPrefixRowStage_full (maskSourceSupport m t) (maskSourceSupport_card m t)) _ g).mpr hD

theorem maskEndpointRootCentered_eq_initial (w : ℕ) :
    targetRootCenteredMask gap C t (maskEndpointLabel gap t) w =
      maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w := by
  funext y
  have ha := maskPrefixRowStage_target_normalizationAnchor
    (maskSourceSupport m t) (maskSourceSupport_card m t) (allNonemptyColumnMasks m).length le_rfl
  rw [maskPrefixRowStage_full] at ha
  change integerDivisorMask (tailMass (primorial w)
    ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w)
      ((fullMaskRowStage (maskSourceSupport m t) (maskSourceSupport_card m t)).rows.normalizationAnchor
        (fullMaskRowStage (maskSourceSupport m t) (maskSourceSupport_card m t)).target))) y - 1 =
    integerDivisorMask (tailMass (primorial w)
      ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w)
        ((maskPrefixRowStage (maskSourceSupport m t) (maskSourceSupport_card m t) 0).rows.normalizationAnchor
          (maskPrefixRowStage (maskSourceSupport m t) (maskSourceSupport_card m t) 0).target))) y - 1
  rw [ha]

theorem maskEndpointFromTerminal_centered_admissible {w : ℕ} (D : MaskIndexedTerminalInput gap C t w)
    (hD : maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D
      (maskInitialCenteredTarget gap C (maskSourceSupport m t) (maskSourceSupport_card m t) w)) :
    rawCenteredSourceAdmissible gap C t (maskEndpointLabel gap t) w
      (maskEndpointSource gap C t (maskEndpointFromTerminal gap C t D)) := by
  have ht := maskEndpointFromTerminal_target gap C t D _ hD
  rw [← maskEndpointRootCentered_eq_initial gap C t w] at ht
  exact maskEndpointSource_centered_admissible gap C t _ ht

theorem maskEndpointFromTerminal_rawCorrelation {w : ℕ} (D : MaskIndexedTerminalInput gap C t w) :
    maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C D =
      rawCorrelation gap a C t (fun _ => maskEndpointSource gap C t (maskEndpointFromTerminal gap C t D)) w := by
  rw [← maskEndpointFromTerminal_correlation gap a C t D]
  exact maskEndpointSource_correlation gap a C t _

end Hindman168
