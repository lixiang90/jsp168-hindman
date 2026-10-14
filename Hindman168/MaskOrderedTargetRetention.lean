import Hindman168.MaskOrderedInputPath

/-! The distinguished row keeps its original function throughout the
actual ordered chain. Its maximum-support normalization anchor and
original tail majorant are also unchanged. This preserves centering
data, without asserting the still-required additive endpoint decay. -/

namespace Hindman168

open scoped Classical

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))

theorem maskUpdatedRowFunctions_target (F : TargetedMaskRowStage S)
    (U : Finset (Fin (m + 1))) (w : ℕ)
    (f : (Fin F.primeArity → ℕ) → Fin F.rowCount → ℤ → ℝ)
    (ξ : Fin (F.step hS U).primeArity → ℕ) (t : ℤ) :
    maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS) F.rows w f ξ
      (F.step hS U).target t = f (maskFreshOldTuple ξ) F.target t := by
  let P := chosenMaskColumnPlan S U hS
  have hi := P.tracked_noninvariant hS (F.rows.row F.target) F.target_support
  have he : maskFreshTuple (maskFreshOldTuple ξ)
      (P.freshValues (P.freshPair (maskFreshNewTuple ξ)).1 (P.freshPair (maskFreshNewTuple ξ)).2) = ξ := by
    rw [P.freshValues_pair, maskFreshTuple_projections]
  have ht := maskUpdatedRowFunctions_tracked gap C P F.rows w f (maskFreshOldTuple ξ)
    (P.freshPair (maskFreshNewTuple ξ)).1 (P.freshPair (maskFreshNewTuple ξ)).2 F.target hi false t
  change maskUpdatedRowFunctions gap C P F.rows w f ξ (maskTrackedRowIndex F.rows P.tag F.target hi false) t = _
  simpa only [he] using ht

theorem TargetedMaskRowStage.step_target_normalizationAnchor (F : TargetedMaskRowStage S)
    (U : Finset (Fin (m + 1))) :
    (F.step hS U).rows.normalizationAnchor (F.step hS U).target =
      F.rows.normalizationAnchor F.target := by
  let P := chosenMaskColumnPlan S U hS
  have hi := P.tracked_noninvariant hS (F.rows.row F.target) F.target_support
  change (F.rows.flattenedMaskStep P.tag).normalizationAnchor
    (maskTrackedRowIndex F.rows P.tag F.target hi false) = _
  exact F.rows.flattenedMaskStep_normalizationAnchor P.tag (maskNoninvariantCopy F.rows P.tag F.target hi false)

def maskStageInputHasTarget {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (g : ℤ → ℝ) : Prop :=
  ∀ x, D.rows x (maskPrefixRowStage S hS k).target = g

def maskRowStageInputHasTarget {F : TargetedMaskRowStage S} {w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (D : MaskRowStageInput S gap C F w T) (g : ℤ → ℝ) : Prop :=
  ∀ x, D.rows x F.target = g

theorem maskRowStageInputTransport_hasTarget {F G : TargetedMaskRowStage S} {w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (h : F = G) (D : MaskRowStageInput S gap C F w T) (g : ℤ → ℝ) :
    maskRowStageInputHasTarget S gap C (maskRowStageInputTransport S gap C h D) g ↔
      maskRowStageInputHasTarget S gap C D g := by
  cases h
  rfl

theorem maskStageStepRowInput_hasTarget {k w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (hw : maskStageUpdatesValid S hS gap C w) (D : MaskStageCorrelationInput S hS gap C k w T)
    (U : Finset (Fin (m + 1))) (g : ℤ → ℝ) (hD : maskStageInputHasTarget S hS gap C D g) :
    maskRowStageInputHasTarget S gap C (maskStageStepRowInput S hS gap C hw D U) g := by
  intro ξ
  funext t
  change maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS)
    (maskPrefixRowStage S hS k).rows w D.rows ξ ((maskPrefixRowStage S hS k).step hS U).target t = g t
  rw [maskUpdatedRowFunctions_target]
  exact congrFun (hD (maskFreshOldTuple ξ)) t

theorem maskStageInputNext_hasTarget {w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (hw : maskStageUpdatesValid S hS gap C w) (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w T) (g : ℤ → ℝ)
    (hD : maskStageInputHasTarget S hS gap C D g) :
    maskStageInputHasTarget S hS gap C (maskStageInputNext S hS gap C hw k D) g := by
  have hs := maskStageStepRowInput_hasTarget S hS gap C hw D (maskCurrentColumnMask m k) g hD
  exact (maskRowStageInputTransport_hasTarget S gap C (maskPrefixRowStage_succ S hS k).symm _ g).mpr hs

theorem maskStageInputFamilyTransport_hasTarget {k w : ℕ}
    {T T' : Finset (Finset (Fin (m + 1)))} (h : T = T')
    (D : MaskStageCorrelationInput S hS gap C k w T) (g : ℤ → ℝ) :
    maskStageInputHasTarget S hS gap C (maskStageInputFamilyTransport S hS gap C h D) g ↔
      maskStageInputHasTarget S hS gap C D g := by
  cases h
  rfl

theorem maskOrderedInputNext_hasTarget {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w (maskRemainingMasks m k.val))
    (g : ℤ → ℝ) (hD : maskStageInputHasTarget S hS gap C D g) :
    maskStageInputHasTarget S hS gap C (maskOrderedInputNext S hS gap C hw k D) g := by
  unfold maskOrderedInputNext
  apply (maskStageInputFamilyTransport_hasTarget S hS gap C _ _ g).mpr
  exact maskStageInputNext_hasTarget S hS gap C hw k D g hD

theorem maskOrderedInputPath_hasTarget {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0))
    (g : ℤ → ℝ) (hD : maskStageInputHasTarget S hS gap C D g)
    (k : ℕ) (hk : k ≤ (allNonemptyColumnMasks m).length) :
    maskStageInputHasTarget S hS gap C (maskOrderedInputPath S hS gap C hw D k hk) g := by
  induction k with
  | zero => exact hD
  | succ k ih =>
    rw [maskOrderedInputPath]
    exact maskOrderedInputNext_hasTarget S hS gap C hw _ _ g (ih (by omega))

theorem maskOrderedTerminalInput_hasTarget {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0))
    (g : ℤ → ℝ) (hD : maskStageInputHasTarget S hS gap C D g) :
    maskStageInputHasTarget S hS gap C (maskOrderedTerminalInput S hS gap C hw D) g := by
  unfold maskOrderedTerminalInput
  apply (maskStageInputFamilyTransport_hasTarget S hS gap C _ _ g).mpr
  exact maskOrderedInputPath_hasTarget S hS gap C hw D g hD _ le_rfl

theorem maskPrefixRowStage_target_normalizationAnchor (k : ℕ)
    (hk : k ≤ (allNonemptyColumnMasks m).length) :
    (maskPrefixRowStage S hS k).rows.normalizationAnchor (maskPrefixRowStage S hS k).target =
      (maskPrefixRowStage S hS 0).rows.normalizationAnchor (maskPrefixRowStage S hS 0).target := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [maskPrefixRowStage_succ S hS ⟨k, by omega⟩,
      TargetedMaskRowStage.step_target_normalizationAnchor]
    exact ih (by omega)

theorem maskPrefixRowStage_target_majorant (k : ℕ)
    (hk : k ≤ (allNonemptyColumnMasks m).length) (w : ℕ) (t : ℤ) :
    maskStageRowMajorant S hS gap C k w (maskPrefixRowStage S hS k).target t =
      maskStageRowMajorant S hS gap C 0 w (maskPrefixRowStage S hS 0).target t := by
  unfold maskStageRowMajorant maskStageRowDivisorMass
  rw [maskPrefixRowStage_target_normalizationAnchor S hS k hk]

end Hindman168
