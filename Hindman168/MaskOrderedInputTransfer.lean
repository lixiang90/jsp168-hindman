import Hindman168.MaskOrderedPrefixSteps

/-! Transfer genuine updated functions into the next actual ordered
prefix. The auxiliary stage data only enables equality transport; all
uniform analytic bounds still apply to the actual prefix stages. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

structure MaskRowStageInput {m N : ℕ} (S : Finset (Fin (m + 1)))
    (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1)) (F : TargetedMaskRowStage S)
    (w : ℕ) (T : Finset (Finset (Fin (m + 1)))) where
  rows : (Fin F.primeArity → ℕ) → Fin F.rowCount → ℤ → ℝ
  masks : (Fin F.primeArity → ℕ) → Finset (Fin (m + 1)) → ℤ → ℝ
  row_bound : ∀ x ∈ (monomialRowPrimeMass m gap F.primeArity w).support, ∀ i t,
    |rows x i t| ≤ maskFamilyRowMajorant gap C F.rows w i t
  mask_bound : ∀ x ∈ (monomialRowPrimeMass m gap F.primeArity w).support,
    ∀ V ∈ T, ∀ t, |masks x V t| ≤ 1

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))

noncomputable def maskStageInput_toRowStageInput {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (D : MaskStageCorrelationInput S hS gap C k w T) :
    MaskRowStageInput S gap C (maskPrefixRowStage S hS k) w T where
  rows := D.rows
  masks := D.masks
  row_bound := D.row_bound
  mask_bound := D.mask_bound

noncomputable def maskRowStageInput_toStageInput {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskRowStageInput S gap C (maskPrefixRowStage S hS k) w T) :
    MaskStageCorrelationInput S hS gap C k w T where
  rows := D.rows
  masks := D.masks
  row_bound := D.row_bound
  mask_bound := D.mask_bound

noncomputable def maskRowStageInputTransport {F G : TargetedMaskRowStage S} {w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (h : F = G) (D : MaskRowStageInput S gap C F w T) :
    MaskRowStageInput S gap C G w T := h ▸ D

noncomputable def maskRowStageInputCorrelation {F : TargetedMaskRowStage S} {w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (D : MaskRowStageInput S gap C F w T) : ℝ :=
  maskRowMaskCorrelation gap C F.rows
    (masterColumnCoefficient N a (fun w => (C w).block) w) w T D.masks D.rows

theorem maskRowStageInputTransport_correlation {F G : TargetedMaskRowStage S} {w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (h : F = G) (D : MaskRowStageInput S gap C F w T) :
    maskRowStageInputCorrelation S gap a C (maskRowStageInputTransport S gap C h D) =
      maskRowStageInputCorrelation S gap a C D := by
  cases h
  rfl

theorem maskRowStageInput_toStageInput_correlation {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskRowStageInput S gap C (maskPrefixRowStage S hS k) w T) :
    maskStageInputCorrelation S hS gap a C (maskRowStageInput_toStageInput S hS gap C D) =
      maskRowStageInputCorrelation S gap a C D := rfl

def maskStageUpdatesValid (w : ℕ) : Prop :=
  ∀ k U T (D : MaskStageCorrelationInput S hS gap C k w T),
    ∀ ξ ∈ (monomialRowPrimeMass m gap ((maskPrefixRowStage S hS k).step hS U).primeArity w).support,
    ∀ i t, |maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS)
      (maskPrefixRowStage S hS k).rows w D.rows ξ i t| ≤
        maskFamilyRowMajorant gap C ((maskPrefixRowStage S hS k).step hS U).rows w i t

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskStageUpdates_eventually_valid : ∀ᶠ w in atTop, maskStageUpdatesValid S hS gap C w := by
  filter_upwards [maskStageUpdatedRowFunctions_eventually_support_bound gap C hC htail S hS] with w hw
  intro k U T D
  exact hw k U D.rows D.row_bound

noncomputable def maskStageStepRowInput {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (hw : maskStageUpdatesValid S hS gap C w)
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1))) :
    MaskRowStageInput S gap C ((maskPrefixRowStage S hS k).step hS U) w (T.erase U) where
  rows := maskUpdatedRowFunctions gap C (chosenMaskColumnPlan S U hS)
    (maskPrefixRowStage S hS k).rows w D.rows
  masks := maskUpdatedMultiplicativeMasks (chosenMaskColumnPlan S U hS) D.masks
  row_bound := hw k U T D
  mask_bound := maskUpdatedMultiplicativeMasks_support_bound gap (chosenMaskColumnPlan S U hS)
    (T.erase U) w D.masks (fun x hx V hV => D.mask_bound x hx V (Finset.mem_of_mem_erase hV))

noncomputable def maskStageInputNext {w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (hw : maskStageUpdatesValid S hS gap C w) (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w T) :
    MaskStageCorrelationInput S hS gap C (k.val+1) w (T.erase (maskCurrentColumnMask m k)) :=
  maskRowStageInput_toStageInput S hS gap C
    (maskRowStageInputTransport S gap C (maskPrefixRowStage_succ S hS k).symm
      (maskStageStepRowInput S hS gap C hw D (maskCurrentColumnMask m k)))

theorem maskStageInputNext_correlation {w : ℕ} {T : Finset (Finset (Fin (m + 1)))}
    (hw : maskStageUpdatesValid S hS gap C w) (k : Fin (allNonemptyColumnMasks m).length)
    (D : MaskStageCorrelationInput S hS gap C k.val w T) :
    maskStageInputCorrelation S hS gap a C (maskStageInputNext S hS gap C hw k D) =
      maskStageNextInputCorrelation S hS gap a C D (maskCurrentColumnMask m k) := by
  unfold maskStageInputNext
  rw [maskRowStageInput_toStageInput_correlation, maskRowStageInputTransport_correlation]
  rfl

end Hindman168
