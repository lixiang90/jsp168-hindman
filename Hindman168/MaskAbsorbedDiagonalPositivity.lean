import Hindman168.MaskUpdatedCorrelationLaw

/-! The absorbed diagonal is nonnegative: both branches coincide there.
Consequently the signed off-diagonal average is bounded above by the
complete next-stage average, with no restoration error or conditioning. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)

noncomputable def maskStageAbsorbedDoubleTest (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (H : MaskStagePoint S hS k → ℝ) (r : MaskStagePoint S hS k) (pq : ℕ × ℕ) : ℝ :=
  maskStageDensity S hS gap a C k U w
    (r.1, (chosenMaskColumnPlan S U hS).absorptionCoordinates pq.1 pq.2 r.2) *
  H (r.1, (chosenMaskColumnPlan S U hS).absorbedCoordinates pq.1 pq.2 r.2) *
  H (r.1, (chosenMaskColumnPlan S U hS).absorbedCoordinates pq.2 pq.1 r.2)

include hC in
theorem maskStageAbsorbedDoubleTest_eventually_diagonal_nonneg :
    ∀ᶠ w in atTop, ∀ k U H r p,
      0 ≤ maskStageAbsorbedDoubleTest S hS gap a C k U w H r (p,p) := by
  filter_upwards [maskStageDensity_eventually_nonneg S hS gap a C hC] with w hw
  intro k U H r p
  unfold maskStageAbsorbedDoubleTest
  dsimp only
  rw [mul_assoc, ← sq]
  exact mul_nonneg (hw k U _) (sq_nonneg _)

include hC in
theorem maskStageAbsorbedDiagonal_eventually_nonneg :
    ∀ᶠ w in atTop, ∀ k U H,
      0 ≤ maskStageFreshDiagonalAverage S hS gap C k w
        (maskStageAbsorbedDoubleTest S hS gap a C k U w H) := by
  filter_upwards [maskStageAbsorbedDoubleTest_eventually_diagonal_nonneg S hS gap a C hC,
    maskStageOuterMass_eventually_nonneg S hS gap C hC] with w hd hμ
  intro k U H
  unfold maskStageFreshDiagonalAverage maskStageFreshPairAverage
  apply expectation_nonneg _ _ (hμ k)
  intro r
  apply expectation_nonneg _ _ (tensor_nonneg _ _ (primePoolMass_nonneg _ _) (primePoolMass_nonneg _ _))
  intro pq
  by_cases he : pq.1 = pq.2
  · simp only [if_pos he]
    have hpair : pq = (pq.1,pq.1) := Prod.ext rfl he.symm
    rw [hpair]
    exact hd k U H r pq.1
  · simp only [if_neg he, le_refl]

include hC in
theorem maskStageAbsorbedOffDiagonal_eventually_le_full :
    ∀ᶠ w in atTop, ∀ k U H,
      maskStageFreshOffDiagonalAverage S hS gap C k w
        (maskStageAbsorbedDoubleTest S hS gap a C k U w H) ≤
      maskStageFreshPairAverage S hS gap C k w
        (maskStageAbsorbedDoubleTest S hS gap a C k U w H) := by
  filter_upwards [maskStageAbsorbedDiagonal_eventually_nonneg S hS gap a C hC] with w hw
  intro k U H
  rw [maskStageFreshPairAverage_split]
  exact le_add_of_nonneg_right (hw k U H)

end Hindman168
