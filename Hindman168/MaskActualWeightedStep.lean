import Hindman168.MaskNormalizedDoubleAbsorption
import Hindman168.MaskRemovalWeightedOffDiagonal

/-! The weighted square applied to the genuine current-mask input.
Outside plans keep the full two-prime square. Balanced plans delete only
the pre-absorption diagonal, absorb pq, then use nonnegative restoration. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

namespace MaskColumnPlan

variable {m N : ℕ} {S U : Finset (Fin (m + 1))}

noncomputable def branchErrorCap (P : MaskColumnPlan S U) (gap : ℕ → Fin N)
    (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (w : ℕ) : ℝ :=
  match P with
  | .outside _ _ _ => 0
  | .balanced u _ _ _ _ _ _ =>
      maskWeightedDiagonalLoss gap C hC u (2 * maskRowCountBound m) w +
        (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
          |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (6 * maskRowCountBound m) *
            masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w|

end MaskColumnPlan

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hgap in
theorem maskPlanBranchErrorCap_tendsto {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) :
    Tendsto (P.branchErrorCap gap C hC) atTop (𝓝 0) := by
  have hc := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  cases P with
  | outside u hu hU => exact tendsto_const_nhds
  | balanced u v hu hv huU hvU hne =>
    change Tendsto (fun w => maskWeightedDiagonalLoss gap C hC u (2 * maskRowCountBound m) w +
      (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
        |((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (6 * maskRowCountBound m) *
          masterPrimePairDilationErrorCap (maskGeneratedMaster m gap) gap (maskOriginalPivotIndex C hC u) w|)
      atTop (𝓝 0)
    have hd := maskWeightedDiagonalLoss_tendsto_zero gap C hC hgap u (2 * maskRowCountBound m)
    have ha := ((hc.prime_pair_dilation_weighted_cap_tendsto gap (maskOriginalPivotIndex C hC u)
      (hgap.mono (fun w hw => hw u)) (6 * maskRowCountBound m)).abs).const_mul
        (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1)
    simpa only [abs_zero, mul_zero, zero_add] using hd.add ha

noncomputable def maskStageFreshNormalizedTest {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (D : MaskStageCorrelationInput S hS gap C k w T)
    (U : Finset (Fin (m + 1))) (r : MaskStagePoint S hS k) (p : ℕ) : ℝ :=
  (chosenMaskColumnPlan S U hS).eta p r.2 *
    maskStageNormalizedInputTest S hS gap a C D U
      (r.1, (chosenMaskColumnPlan S U hS).coordinates p r.2)

include hC htail in
theorem maskStageFreshNormalizedTest_eventually_bound :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U,
      ∀ r ∈ (maskStageOuterMass S hS gap C k w).support, ∀ p,
      |maskStageFreshNormalizedTest S hS gap a C D U r p| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) *
          (chosenMaskColumnPlan S U hS).eta p r.2 := by
  filter_upwards [maskStageNormalizedInputTest_eventually_bound S hS gap a C hC htail] with w hw
  intro k T D U r hr p
  have hb := hw k T D U r.1 (maskStageOuterMass_support_old S hS gap C k w r hr)
    ((chosenMaskColumnPlan S U hS).coordinates p r.2)
  unfold maskStageFreshNormalizedTest
  rw [abs_mul, abs_of_nonneg ((chosenMaskColumnPlan S U hS).eta_nonneg p r.2)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb ((chosenMaskColumnPlan S U hS).eta_nonneg p r.2)

include ha hC hgap htail in
theorem maskStageSubstitutedInputAverage_eventually_square_step (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop, ∀ T (D : MaskStageCorrelationInput S hS gap C k w T), U ∈ T →
      |maskStageSubstitutedInputAverage S hS gap a C D U| ^ 2 ≤
        (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
          |maskStageNextInputCorrelation S hS gap a C D U| +
        (chosenMaskColumnPlan S U hS).branchErrorCap gap C hC w := by
  cases hP : chosenMaskColumnPlan S U hS with
  | outside u hu hU =>
    filter_upwards [maskStageSubstitutedInputAverage_eventually_extracted S hS gap a C hC htail,
      maskRemoval_weighted_square_constant_cap S hS gap a ha C hC hgap htail k U,
      maskStageNextInputCorrelation_eventually_absorbed S hS gap a C hC htail] with w he hs hn
    intro T D hUT
    have hb : ∀ r ∈ (maskStageOuterMass S hS gap C k w).support,
        |D.masks r.1 U (maskCoordinateMonomial U r.2)| ≤ 1 := by
      intro r hr
      exact D.mask_bound r.1 (maskStageOuterMass_support_old S hS gap C k w r hr) U hUT _
    have hsq := hs (fun r => D.masks r.1 U (maskCoordinateMonomial U r.2)) hb
      (maskStageFreshNormalizedTest S hS gap a C D U)
    change |expectation (maskStageOuterMass S hS gap C k w) (fun r =>
      D.masks r.1 U (maskCoordinateMonomial U r.2) * maskStageDensity S hS gap a C k U w r *
        expectation (maskFreshPrimeMass (m := m) gap w) (maskStageFreshNormalizedTest S hS gap a C D U r))| ^ 2 ≤
      (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) * maskStageFreshPairAverage S hS gap C k w
        (fun r pq => maskStageDensity S hS gap a C k U w r *
          maskStageFreshNormalizedTest S hS gap a C D U r pq.1 *
          maskStageFreshNormalizedTest S hS gap a C D U r pq.2) at hsq
    have hI := he k T D U hUT
    change maskStageSubstitutedInputAverage S hS gap a C D U =
      expectation (maskStageOuterMass S hS gap C k w) (fun r =>
        D.masks r.1 U (maskCoordinateMonomial U r.2) * maskStageDensity S hS gap a C k U w r *
          expectation (maskFreshPrimeMass (m := m) gap w)
            (maskStageFreshNormalizedTest S hS gap a C D U r)) at hI
    rw [← hI] at hsq
    dsimp only [maskStageFreshNormalizedTest] at hsq
    have hW : (fun r pq => maskStageDensity S hS gap a C k U w r *
        ((chosenMaskColumnPlan S U hS).eta pq.1 r.2 *
          maskStageNormalizedInputTest S hS gap a C D U
            (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.1 r.2)) *
        ((chosenMaskColumnPlan S U hS).eta pq.2 r.2 *
          maskStageNormalizedInputTest S hS gap a C D U
            (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.2 r.2))) =
        maskStageAbsorbedDoubleTest S hS gap a C k U w
          (maskStageNormalizedInputTest S hS gap a C D U) := by
      funext r pq
      unfold maskStageAbsorbedDoubleTest
      rw [hP]
      simp only [MaskColumnPlan.eta, one_mul]
      rfl
    rw [hW, ← hn k T D U] at hsq
    simp only [MaskColumnPlan.branchErrorCap, add_zero]
    exact hsq.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  | balanced u v hu hv huU hvU hne =>
    filter_upwards [maskStageSubstitutedInputAverage_eventually_extracted S hS gap a C hC htail,
      maskStageFreshNormalizedTest_eventually_bound S hS gap a C hC htail,
      maskRemoval_weighted_square_offDiagonal S hS gap a ha C hC hgap htail k U u (2 * maskRowCountBound m),
      maskStageNormalizedDoubleTest_eventually_absorption_bound S hS gap a C hC hgap htail
        k U u v hu hv huU hvU hne hP,
      maskStageNextInputCorrelation_eventually_dominates_offDiagonal S hS gap a C hC htail]
      with w he hg hs hab hn
    intro T D hUT
    have hb : ∀ r ∈ (maskStageOuterMass S hS gap C k w).support,
        |D.masks r.1 U (maskCoordinateMonomial U r.2)| ≤ 1 := by
      intro r hr
      exact D.mask_bound r.1 (maskStageOuterMass_support_old S hS gap C k w r hr) U hUT _
    have hgb : ∀ r ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ p ∈ (maskFreshPrimeMass (m := m) gap w).support,
        |maskStageFreshNormalizedTest S hS gap a C D U r p| ≤
          ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) *
            primeDivisorEta p (r.2 u) := by
      intro r hr p _
      simpa only [hP, MaskColumnPlan.eta] using hg k T D U r hr p
    have hsq := hs (fun r => D.masks r.1 U (maskCoordinateMonomial U r.2)) hb
      (maskStageFreshNormalizedTest S hS gap a C D U) hgb
    have hI := he k T D U hUT
    change maskStageSubstitutedInputAverage S hS gap a C D U =
      expectation (maskStageOuterMass S hS gap C k w) (fun r =>
        D.masks r.1 U (maskCoordinateMonomial U r.2) * maskStageDensity S hS gap a C k U w r *
          expectation (maskFreshPrimeMass (m := m) gap w)
            (maskStageFreshNormalizedTest S hS gap a C D U r)) at hI
    rw [← hI] at hsq
    dsimp only [maskStageFreshNormalizedTest] at hsq
    have hW : (fun r pq => maskStageDensity S hS gap a C k U w r *
        ((chosenMaskColumnPlan S U hS).eta pq.1 r.2 *
          maskStageNormalizedInputTest S hS gap a C D U
            (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.1 r.2)) *
        ((chosenMaskColumnPlan S U hS).eta pq.2 r.2 *
          maskStageNormalizedInputTest S hS gap a C D U
            (r.1, (chosenMaskColumnPlan S U hS).coordinates pq.2 r.2))) =
        fun r pq => primeDivisorEta pq.1 (r.2 u) * primeDivisorEta pq.2 (r.2 u) *
          maskStageNormalizedDoubleTest S hS gap a C D U r pq := by
      funext r pq
      unfold maskStageNormalizedDoubleTest
      rw [hP]
      simp only [MaskColumnPlan.eta]
      ring
    rw [hW] at hsq
    have heabs := hab T D
    have hupper := (le_abs_self _).trans heabs
    have hmul := mul_le_mul_of_nonneg_left hupper
      (show (0 : ℝ) ≤ (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) by positivity)
    have hnext := mul_le_mul_of_nonneg_left ((hn k T D U).trans (le_abs_self _))
      (show (0 : ℝ) ≤ (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) by positivity)
    simp only [MaskColumnPlan.branchErrorCap]
    linarith

end Hindman168
