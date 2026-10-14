import Hindman168.MaskFiniteSquareThresholds
import Hindman168.MaskOrderedTargetRetention

/-! Eliminate every actual multiplicative mask with finite uniform error
thresholds. The genuine mask-free endpoint retains the distinguished
function. Its additive decay is an explicit remaining hypothesis in the
last implication, not an axiom or an asserted completed proof. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

noncomputable def maskRemovalSquareConstant (m : ℕ) : ℝ :=
  ((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1

theorem maskRemovalSquareConstant_ge_one (m : ℕ) : 1 ≤ maskRemovalSquareConstant m := by
  unfold maskRemovalSquareConstant
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include ha hC hgap htail in
theorem maskOrderedSquareSteps_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ k : Fin (allNonemptyColumnMasks m).length, ∀ T
      (D : MaskStageCorrelationInput S hS gap C k.val w T), maskCurrentColumnMask m k ∈ T →
      |maskStageInputCorrelation S hS gap a C D| ^ 2 ≤
        maskRemovalSquareConstant m * |maskStageNextInputCorrelation S hS gap a C D (maskCurrentColumnMask m k)| +
          maskSquareTolerance (maskRemovalSquareConstant m) ε (k.val+1) := by
  apply eventually_all.mpr
  intro k
  exact maskStageInputCorrelation_uniform_square_step S hS gap a ha C hC hgap htail k.val
    (maskCurrentColumnMask m k)
    (maskSquareTolerance_pos ((zero_le_one : (0 : ℝ) ≤ 1).trans (maskRemovalSquareConstant_ge_one m)) hε _)

include ha hC hgap htail in
theorem maskOrderedInputPath_eventually_control {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ (hw : maskStageUpdatesValid S hS gap C w)
      (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)),
      |maskStageInputCorrelation S hS gap a C (maskOrderedTerminalInput S hS gap C hw D)| ≤
        maskSquareTolerance (maskRemovalSquareConstant m) ε (allNonemptyColumnMasks m).length →
      |maskStageInputCorrelation S hS gap a C D| ≤ ε := by
  filter_upwards [maskOrderedSquareSteps_eventually S hS gap a ha C hC hgap htail hε] with w hs
  intro hw D hend
  let L := (allNonemptyColumnMasks m).length
  let x : ℕ → ℝ := fun k => if hk : k ≤ L then
    |maskStageInputCorrelation S hS gap a C (maskOrderedInputPath S hS gap C hw D k hk)| else 0
  have hx : ∀ k ≤ L, 0 ≤ x k := by
    intro k hk
    dsimp only [x]
    rw [dif_pos hk]
    exact abs_nonneg _
  have hstep : ∀ k < L, x k ^ 2 ≤ maskRemovalSquareConstant m * x (k+1) +
      maskSquareTolerance (maskRemovalSquareConstant m) ε (k+1) := by
    intro k hk
    dsimp only [x]
    rw [dif_pos (by omega : k ≤ L), dif_pos (by omega : k+1 ≤ L)]
    let j : Fin (allNonemptyColumnMasks m).length := ⟨k, hk⟩
    have h := hs j (maskRemainingMasks m k) (maskOrderedInputPath S hS gap C hw D k (by omega))
      (maskCurrentColumnMask_mem_remaining m j)
    rw [← maskOrderedInputPath_succ_correlation S hS gap a C hw D j] at h
    exact h
  have he : x L ≤ maskSquareTolerance (maskRemovalSquareConstant m) ε L := by
    dsimp only [x]
    rw [dif_pos le_rfl]
    rw [← maskOrderedTerminalInput_correlation]
    exact hend
  have h0 := finite_mask_square_backward
    ((zero_le_one : (0 : ℝ) ≤ 1).trans (maskRemovalSquareConstant_ge_one m)) hε L x hx hstep he
  change |maskStageInputCorrelation S hS gap a C D| ≤ ε at h0
  exact h0

include ha hC hgap htail in
theorem maskFiniteElimination_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ (g : ℤ → ℝ)
      (D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0)),
      maskStageInputHasTarget S hS gap C D g →
      ∃ E : MaskStageCorrelationInput S hS gap C (allNonemptyColumnMasks m).length w ∅,
        maskStageInputHasTarget S hS gap C E g ∧
        (|maskStageInputCorrelation S hS gap a C E| ≤
          ε ^ (2 ^ (allNonemptyColumnMasks m).length) /
            (maskRemovalSquareConstant m + 1) ^ (2 ^ (allNonemptyColumnMasks m).length - 1) →
          |maskStageInputCorrelation S hS gap a C D| ≤ ε) := by
  filter_upwards [maskStageUpdates_eventually_valid S hS gap C hC htail,
    maskOrderedInputPath_eventually_control S hS gap a ha C hC hgap htail hε] with w hw hc
  intro g D hD
  refine ⟨maskOrderedTerminalInput S hS gap C hw D,
    maskOrderedTerminalInput_hasTarget S hS gap C hw D g hD, ?_⟩
  intro he
  apply hc hw D
  simpa only [maskSquareTolerance_closed] using he

include ha hC hgap htail in
theorem maskFiniteElimination_uniform_centered (g : ℕ → ℤ → ℝ)
    (hend : ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ E : MaskStageCorrelationInput S hS gap C (allNonemptyColumnMasks m).length w ∅,
        maskStageInputHasTarget S hS gap C E (g w) → |maskStageInputCorrelation S hS gap a C E| ≤ η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ D : MaskStageCorrelationInput S hS gap C 0 w (maskRemainingMasks m 0),
        maskStageInputHasTarget S hS gap C D (g w) → |maskStageInputCorrelation S hS gap a C D| ≤ ε := by
  intro ε hε
  have hη := maskSquareTolerance_pos
    ((zero_le_one : (0 : ℝ) ≤ 1).trans (maskRemovalSquareConstant_ge_one m)) hε
    (allNonemptyColumnMasks m).length
  rw [maskSquareTolerance_closed] at hη
  filter_upwards [maskFiniteElimination_eventually S hS gap a ha C hC hgap htail hε,
    hend _ hη] with w hm he
  intro D hD
  obtain ⟨E, hE, hb⟩ := hm (g w) D hD
  exact hb (he E hE)

end Hindman168
