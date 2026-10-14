import Hindman168.MaskOrderedInputTransfer

/-! Construct every admissible input along the actual finite mask list.
The endpoint has no remaining multiplicative mask, and each adjacent
correlation is exactly the genuine one-step updated correlation. -/

namespace Hindman168

open scoped Classical

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))

noncomputable def maskStageInputFamilyTransport {k w : ℕ}
    {T T' : Finset (Finset (Fin (m + 1)))} (h : T = T')
    (D : MaskStageCorrelationInput S hS gap C k w T) :
    MaskStageCorrelationInput S hS gap C k w T' := h ▸ D

theorem maskStageInputFamilyTransport_correlation {k w : ℕ}
    {T T' : Finset (Finset (Fin (m + 1)))} (h : T = T')
    (D : MaskStageCorrelationInput S hS gap C k w T) :
    maskStageInputCorrelation S hS gap a C (maskStageInputFamilyTransport S hS gap C h D) =
      maskStageInputCorrelation S hS gap a C D := by
  cases h
  rfl

noncomputable def maskOrderedInputNext {w : ℕ}
    (hw : maskStageUpdatesValid S hS gap C w) (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w (maskRemainingMasks m k.val)) :
    MaskStageCorrelationInput S hS gap C (k.val+1) w (maskRemainingMasks m (k.val+1)) :=
  maskStageInputFamilyTransport S hS gap C (maskRemainingMasks_succ m k).symm
    (maskStageInputNext S hS gap C hw k D)

theorem maskOrderedInputNext_correlation {w : ℕ}
    (hw : maskStageUpdatesValid S hS gap C w) (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w (maskRemainingMasks m k.val)) :
    maskStageInputCorrelation S hS gap a C (maskOrderedInputNext S hS gap C hw k D) =
      maskStageNextInputCorrelation S hS gap a C D (maskCurrentColumnMask m k) := by
  unfold maskOrderedInputNext
  rw [maskStageInputFamilyTransport_correlation, maskStageInputNext_correlation]

noncomputable def maskOrderedInputPath {w : ℕ}
    (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)) :
    (k : ℕ) → k ≤ (allNonemptyColumnMasks m).length →
      MaskStageCorrelationInput S hS gap C k w (maskRemainingMasks m k)
  | 0, _ => D
  | k+1, hk => maskOrderedInputNext S hS gap C hw ⟨k, by omega⟩
      (maskOrderedInputPath hw D k (by omega))

theorem maskOrderedInputPath_zero {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)) :
    maskOrderedInputPath S hS gap C hw D 0 (Nat.zero_le _) = D := rfl

theorem maskOrderedInputPath_succ_correlation {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0))
    (k : Fin (allNonemptyColumnMasks m).length) :
    maskStageInputCorrelation S hS gap a C
      (maskOrderedInputPath S hS gap C hw D (k.val+1) (by omega)) =
    maskStageNextInputCorrelation S hS gap a C
      (maskOrderedInputPath S hS gap C hw D k.val (by omega)) (maskCurrentColumnMask m k) := by
  rw [maskOrderedInputPath, maskOrderedInputNext_correlation]

noncomputable def maskOrderedTerminalInput {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)) :
    MaskStageCorrelationInput S hS gap C (allNonemptyColumnMasks m).length w ∅ :=
  maskStageInputFamilyTransport S hS gap C (maskRemainingMasks_full m)
    (maskOrderedInputPath S hS gap C hw D (allNonemptyColumnMasks m).length le_rfl)

theorem maskOrderedTerminalInput_correlation {w : ℕ} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)) :
    maskStageInputCorrelation S hS gap a C (maskOrderedTerminalInput S hS gap C hw D) =
      maskStageInputCorrelation S hS gap a C
        (maskOrderedInputPath S hS gap C hw D (allNonemptyColumnMasks m).length le_rfl) := by
  unfold maskOrderedTerminalInput
  rw [maskStageInputFamilyTransport_correlation]

end Hindman168
