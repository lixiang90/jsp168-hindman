import Hindman168.MaskFinitePowerIteration

/-! The genuine ordered mask path has a complete-law powered endpoint
inequality with one explicit function-independent error tending to zero. -/

namespace Hindman168
open Filter
open scoped Topology Classical

variable {m N : ℕ} (S : Finset (Fin (m+1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskOrderedStepError (k w : ℕ) : ℝ :=
  if hk : k < (allNonemptyColumnMasks m).length then
    |(chosenMaskColumnPlan S (maskCurrentColumnMask m ⟨k,hk⟩) hS).totalStepErrorCap gap C hC w|
  else 0

theorem maskOrderedStepError_nonneg (k w : ℕ) :
    0 ≤ maskOrderedStepError S hS gap C hC k w := by
  unfold maskOrderedStepError
  split_ifs <;> positivity

include hgap in
theorem maskOrderedStepError_tendsto_zero (k : ℕ) :
    Tendsto (maskOrderedStepError S hS gap C hC k) atTop (𝓝 0) := by
  change Tendsto (fun w => maskOrderedStepError S hS gap C hC k w) atTop (𝓝 0)
  by_cases hk : k < (allNonemptyColumnMasks m).length
  · simpa only [maskOrderedStepError, dif_pos hk, abs_zero] using
      (maskPlanTotalStepErrorCap_tendsto gap C hC hgap
        (chosenMaskColumnPlan S (maskCurrentColumnMask m ⟨k,hk⟩) hS)).abs
  · simp only [maskOrderedStepError, dif_neg hk]
    exact tendsto_const_nhds

noncomputable def maskRemovalPowerCoefficient (m : ℕ) : ℝ :=
  maskPowerCoefficient (maskRemovalSquareConstant m) (allNonemptyColumnMasks m).length

theorem maskRemovalPowerCoefficient_ge_one (m : ℕ) : 1 ≤ maskRemovalPowerCoefficient m :=
  maskPowerCoefficient_ge_one (maskRemovalSquareConstant_ge_one m) _

noncomputable def maskOrderedPowerError (w : ℕ) : ℝ :=
  maskPowerError (maskRemovalSquareConstant m) (fun k => maskOrderedStepError S hS gap C hC k w)
    (allNonemptyColumnMasks m).length

theorem maskOrderedPowerError_nonneg (w : ℕ) : 0 ≤ maskOrderedPowerError S hS gap C hC w :=
  maskPowerError_nonneg _ _ (fun k => maskOrderedStepError_nonneg S hS gap C hC k w) _

include hgap in
theorem maskOrderedPowerError_tendsto_zero :
    Tendsto (maskOrderedPowerError S hS gap C hC) atTop (𝓝 0) :=
  maskPowerError_tendsto_zero _ _ (fun k => maskOrderedStepError_tendsto_zero S hS gap C hC hgap k) _

include ha hC hgap htail in
theorem maskOrderedSquareSteps_with_cap :
    ∀ᶠ w in atTop, ∀ k : Fin (allNonemptyColumnMasks m).length, ∀ T
      (D : MaskStageCorrelationInput S hS gap C k.val w T), maskCurrentColumnMask m k ∈ T →
      |maskStageInputCorrelation S hS gap a C D| ^ 2 ≤
        maskRemovalSquareConstant m * |maskStageNextInputCorrelation S hS gap a C D (maskCurrentColumnMask m k)| +
          maskOrderedStepError S hS gap C hC k.val w := by
  have hs : ∀ᶠ w in atTop, ∀ k : Fin (allNonemptyColumnMasks m).length, ∀ T
      (D : MaskStageCorrelationInput S hS gap C k.val w T), maskCurrentColumnMask m k ∈ T →
      |maskStageInputCorrelation S hS gap a C D| ^ 2 ≤
        maskRemovalSquareConstant m * |maskStageNextInputCorrelation S hS gap a C D (maskCurrentColumnMask m k)| +
          (chosenMaskColumnPlan S (maskCurrentColumnMask m k) hS).totalStepErrorCap gap C hC w :=
    eventually_all.mpr (fun k => maskStageInputCorrelation_eventually_square_step S hS gap a ha C hC hgap htail
      k.val (maskCurrentColumnMask m k))
  filter_upwards [hs] with w hw
  intro k T D hD
  simp only [maskOrderedStepError, dif_pos k.isLt]
  exact (hw k T D hD).trans (add_le_add le_rfl (le_abs_self _))

include ha hC hgap htail in
theorem maskOrderedInputPath_eventually_power_output :
    ∀ᶠ w in atTop, ∀ (hw : maskStageUpdatesValid S hS gap C w)
      (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)),
      |maskStageInputCorrelation S hS gap a C D| ^ (2 ^ (allNonemptyColumnMasks m).length) ≤
        maskRemovalPowerCoefficient m *
          |maskStageInputCorrelation S hS gap a C (maskOrderedTerminalInput S hS gap C hw D)| +
        maskOrderedPowerError S hS gap C hC w := by
  filter_upwards [maskOrderedSquareSteps_with_cap S hS gap a ha C hC hgap htail] with w hs
  intro hw D
  let L := (allNonemptyColumnMasks m).length
  let x : ℕ → ℝ := fun k => if hk : k ≤ L then
    |maskStageInputCorrelation S hS gap a C (maskOrderedInputPath S hS gap C hw D k hk)| else 0
  have hx : ∀ k ≤ L, 0 ≤ x k := by
    intro k hk
    dsimp only [x]
    rw [dif_pos hk]
    exact abs_nonneg _
  have hstep : ∀ k < L, x k ^ 2 ≤ maskRemovalSquareConstant m * x (k+1) +
      maskOrderedStepError S hS gap C hC k w := by
    intro k hk
    dsimp only [x]
    rw [dif_pos (by omega : k ≤ L), dif_pos (by omega : k+1 ≤ L)]
    let j : Fin (allNonemptyColumnMasks m).length := ⟨k,hk⟩
    have h := hs j (maskRemainingMasks m k) (maskOrderedInputPath S hS gap C hw D k (by omega))
      (maskCurrentColumnMask_mem_remaining m j)
    rw [← maskOrderedInputPath_succ_correlation S hS gap a C hw D j] at h
    exact h
  have h := finite_mask_power_iteration (maskRemovalSquareConstant m)
    (fun k => maskOrderedStepError S hS gap C hC k w) x L hx hstep L le_rfl
  dsimp only [x] at h
  rw [dif_pos (Nat.zero_le L), dif_pos le_rfl] at h
  change |maskStageInputCorrelation S hS gap a C D| ^ (2 ^ L) ≤
    maskRemovalPowerCoefficient m *
      |maskStageInputCorrelation S hS gap a C (maskOrderedInputPath S hS gap C hw D L le_rfl)| +
    maskOrderedPowerError S hS gap C hC w at h
  rw [← maskOrderedTerminalInput_correlation] at h
  exact h

include ha hC hgap htail in
theorem maskPoweredElimination_eventually :
    ∀ᶠ w in atTop, ∀ g : ℤ → ℝ,
      ∀ D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0),
      maskStageInputHasTarget S hS gap C D g →
      ∃ E : MaskStageCorrelationInput S hS gap C (allNonemptyColumnMasks m).length w ∅,
        maskStageInputHasTarget S hS gap C E g ∧
        |maskStageInputCorrelation S hS gap a C D| ^ (2 ^ (allNonemptyColumnMasks m).length) ≤
          maskRemovalPowerCoefficient m * |maskStageInputCorrelation S hS gap a C E| +
            maskOrderedPowerError S hS gap C hC w := by
  filter_upwards [maskStageUpdates_eventually_valid S hS gap C hC htail,
    maskOrderedInputPath_eventually_power_output S hS gap a ha C hC hgap htail] with w hw hp
  intro g D hD
  exact ⟨maskOrderedTerminalInput S hS gap C hw D,
    maskOrderedTerminalInput_hasTarget S hS gap C hw D g hD, hp hw D⟩

end Hindman168
