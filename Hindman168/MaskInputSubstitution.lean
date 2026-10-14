import Hindman168.MaskInsertionSquaredErrors

/-! Actual chosen-plan substitution for admissible row/mask inputs.
Its error comes from the original one-coordinate or balanced insertion
cap, and its exact normalized expression extracts only the current mask. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))

noncomputable def maskStageSubstitutedInputAverage {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))}
    (D : MaskStageCorrelationInput S hS gap C k w T) (U : Finset (Fin (m + 1))) : ℝ :=
  maskStageSubstitutedAverage S hS gap C k U w (maskStageInputTest S hS gap a C D)

theorem maskStageInputCorrelation_originalTest {k w : ℕ}
    {T : Finset (Finset (Fin (m + 1)))} (D : MaskStageCorrelationInput S hS gap C k w T) :
    maskStageInputCorrelation S hS gap a C D =
      expectation (maskStageOuterMass S hS gap C k w) (maskStageInputTest S hS gap a C D) := by
  exact maskRowMaskCorrelation_originalOuter S hS gap a C k w T D.masks D.rows

variable (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC hgap htail in
theorem maskStageInputCorrelation_eventually_substitution_bound (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop, ∀ T (D : MaskStageCorrelationInput S hS gap C k w T),
      |maskStageInputCorrelation S hS gap a C D - maskStageSubstitutedInputAverage S hS gap a C D U| ≤
        (chosenMaskColumnPlan S U hS).insertionErrorCap gap C hC (2 * maskRowCountBound m) w := by
  cases hP : chosenMaskColumnPlan S U hS with
  | outside u hu hU =>
    filter_upwards [maskStageInputTest_eventually_polynomial_bound S hS gap a C hC htail,
      maskStagePrimeInsertion_bound S hS gap C hC hgap k u (2 * maskRowCountBound m)] with w hB hb
    intro T D
    rw [maskStageInputCorrelation_originalTest]
    have he := hb (maskStageInputTest S hS gap a C D) (hB k T D)
    simpa only [maskStageSubstitutedInputAverage, maskStageSubstitutedAverage,
      maskStagePrimeInsertedAverage, hP, MaskColumnPlan.eta, MaskColumnPlan.coordinates,
      one_mul, MaskColumnPlan.insertionErrorCap] using he
  | balanced u v hu hv huU hvU hne =>
    filter_upwards [maskStageInputTest_eventually_polynomial_bound S hS gap a C hC htail,
      maskStageBalancedPrimeInsertion_bound S hS gap C hC hgap k u v hne (2 * maskRowCountBound m)] with w hB hb
    intro T D
    rw [maskStageInputCorrelation_originalTest]
    have he := hb (maskStageInputTest S hS gap a C D) (hB k T D)
    simpa only [maskStageSubstitutedInputAverage, maskStageSubstitutedAverage,
      maskStageBalancedPrimeAverage, hP, MaskColumnPlan.eta, MaskColumnPlan.coordinates,
      MaskColumnPlan.insertionErrorCap] using he

include hC htail in
theorem maskStageSubstitutedInputAverage_eventually_extracted :
    ∀ᶠ w in atTop, ∀ k T (D : MaskStageCorrelationInput S hS gap C k w T) U, U ∈ T →
      maskStageSubstitutedInputAverage S hS gap a C D U =
      expectation (maskStageOuterMass S hS gap C k w) (fun r =>
        D.masks r.1 U (maskCoordinateMonomial U r.2) * maskStageDensity S hS gap a C k U w r *
          expectation (maskFreshPrimeMass (m := m) gap w) (fun p =>
            (chosenMaskColumnPlan S U hS).eta p r.2 *
              maskStageNormalizedInputTest S hS gap a C D U
                (r.1, (chosenMaskColumnPlan S U hS).coordinates p r.2))) := by
  filter_upwards [maskCurrentNormalizedExtraction_eventually_average S hS gap a C hC htail] with w hw
  intro k T D U hU
  exact hw k U T hU D.masks D.rows

end Hindman168
