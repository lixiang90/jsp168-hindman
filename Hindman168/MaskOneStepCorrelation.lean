import Hindman168.MaskActualWeightedStep

/-! The actual one-step multiplicative-mask correlation recurrence.
The input and output use the original full prime/base laws, the selected
mask is erased, and a derived error tends to zero uniformly in all
admissible input functions at each fixed actual prefix and chosen mask. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

namespace MaskColumnPlan

variable {m N : ℕ} {S U : Finset (Fin (m + 1))}

noncomputable def totalStepErrorCap (P : MaskColumnPlan S U) (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (w : ℕ) : ℝ :=
  maskSquareInsertionLoss ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)
    (P.insertionErrorCap gap C hC (2 * maskRowCountBound m) w) (2 * maskRowCountBound m) +
      P.branchErrorCap gap C hC w

end MaskColumnPlan

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hgap in
theorem maskPlanTotalStepErrorCap_tendsto {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) :
    Tendsto (P.totalStepErrorCap gap C hC) atTop (𝓝 0) := by
  change Tendsto (fun w => maskSquareInsertionLoss
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ)
    (P.insertionErrorCap gap C hC (2 * maskRowCountBound m) w) (2 * maskRowCountBound m) +
      P.branchErrorCap gap C hC w) atTop (𝓝 0)
  simpa only [zero_add] using
    (maskPlanSquaredInsertionLoss_tendsto gap C hC hgap P (2 * maskRowCountBound m)).add
      (maskPlanBranchErrorCap_tendsto gap C hC hgap P)

include ha hC hgap htail in
theorem maskStageInputCorrelation_eventually_square_step (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop, ∀ T (D : MaskStageCorrelationInput S hS gap C k w T), U ∈ T →
      |maskStageInputCorrelation S hS gap a C D| ^ 2 ≤
        (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
          |maskStageNextInputCorrelation S hS gap a C D U| +
        (chosenMaskColumnPlan S U hS).totalStepErrorCap gap C hC w := by
  filter_upwards [maskStageInputCorrelation_eventually_polynomial_bound S hS gap a C hC htail,
    maskStageInputCorrelation_eventually_substitution_bound S hS gap a C hC hgap htail k U,
    maskStageSubstitutedInputAverage_eventually_square_step S hS gap a ha C hC hgap htail k U]
    with w hB hi hs
  intro T D hU
  have he := abs_square_le_square_add_twice_cap_error
    (maskStageInputCorrelation S hS gap a C D)
    (maskStageSubstitutedInputAverage S hS gap a C D U)
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m))
    |(chosenMaskColumnPlan S U hS).insertionErrorCap gap C hC (2 * maskRowCountBound m) w|
    (hB k T D) ((hi T D).trans (le_abs_self _))
  have hsq := hs T D hU
  unfold MaskColumnPlan.totalStepErrorCap maskSquareInsertionLoss
  linarith

include ha hC hgap htail in
theorem maskStageInputCorrelation_uniform_square_step (k : ℕ) (U : Finset (Fin (m + 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ T (D : MaskStageCorrelationInput S hS gap C k w T), U ∈ T →
      |maskStageInputCorrelation S hS gap a C D| ^ 2 ≤
        (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
          |maskStageNextInputCorrelation S hS gap a C D U| + ε := by
  filter_upwards [maskStageInputCorrelation_eventually_square_step S hS gap a ha C hC hgap htail k U,
    (maskPlanTotalStepErrorCap_tendsto gap C hC hgap (chosenMaskColumnPlan S U hS)).eventually
      (eventually_lt_nhds hε)] with w hs he
  intro T D hU
  exact (hs T D hU).trans (by linarith)

end Hindman168
