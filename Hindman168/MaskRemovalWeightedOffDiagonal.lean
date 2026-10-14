import Hindman168.MaskRemovalStageDivisorCaps

/-! The actual weighted square with the fresh-prime diagonal deleted.
The m-only prefactor and all old-prime/harmonic weights are retained.
The remaining off-diagonal average is signed and is not asserted to be
positive; its possible deficit is covered by the derived vanishing loss.
Prime insertion and off-diagonal branch absorption remain separate steps. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskWeightedDiagonalLoss (col : Fin (m + 1)) (B w : ℕ) : ℝ :=
  (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
      (2 * maskRowCountBound m + 2 * B) * maskFreshWeightedDiagonalCap gap C hC col w)

include hgap in
theorem maskWeightedDiagonalLoss_tendsto_zero (col : Fin (m + 1)) (B : ℕ) :
    Tendsto (maskWeightedDiagonalLoss gap C hC col B) atTop (𝓝 0) := by
  unfold maskWeightedDiagonalLoss
  simpa only [mul_zero] using
    (maskFreshWeightedDiagonalCap_weighted_tendsto gap C hC hgap col
      (2 * maskRowCountBound m + 2 * B)).const_mul (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1)

include ha hC hgap htail in
theorem maskRemoval_weighted_square_offDiagonal (k : ℕ) (U : Finset (Fin (m + 1)))
    (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ b : MaskStagePoint S hS k → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support, |b p| ≤ 1) →
      ∀ g : MaskStagePoint S hS k → ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ q ∈ (maskFreshPrimeMass (m := m) gap w).support,
        |g p q| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B * primeDivisorEta q (p.2 col)) →
      |expectation (maskStageOuterMass S hS gap C k w) (fun p =>
        b p * maskStageDensity S hS gap a C k U w p * expectation (maskFreshPrimeMass (m := m) gap w) (g p))| ^ 2 ≤
      (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
        maskStageFreshOffDiagonalAverage S hS gap C k w (fun p pq =>
          maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2) +
            maskWeightedDiagonalLoss gap C hC col B w := by
  filter_upwards [maskRemoval_weighted_square_constant_cap S hS gap a ha C hC hgap htail k U,
    maskStageWeightedDouble_integrand_bound S hS gap a C hC htail k U col B,
    maskStageFreshDiagonalAverage_bound S hS gap C hC k col (2 * maskRowCountBound m + 2 * B)]
    with w hs hi hd
  intro b hb g hg
  let H : MaskStagePoint S hS k → ℕ × ℕ → ℝ := fun p pq =>
    maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2
  have he := hd H (hi g hg)
  have hupper := (le_abs_self (maskStageFreshDiagonalAverage S hS gap C k w H)).trans he
  have hh := hs b hb g
  change |expectation (maskStageOuterMass S hS gap C k w) (fun p =>
    b p * maskStageDensity S hS gap a C k U w p * expectation (maskFreshPrimeMass (m := m) gap w) (g p))| ^ 2 ≤
    (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) * maskStageFreshPairAverage S hS gap C k w H at hh
  rw [maskStageFreshPairAverage_split] at hh
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0 : ℝ) ≤ (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) by positivity)
  unfold maskWeightedDiagonalLoss
  dsimp [H] at hh hm
  linarith

include ha hC hgap htail in
theorem maskRemoval_weighted_square_offDiagonal_uniform_zero (k : ℕ) (U : Finset (Fin (m + 1)))
    (col : Fin (m + 1)) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ b : MaskStagePoint S hS k → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support, |b p| ≤ 1) →
      ∀ g : MaskStagePoint S hS k → ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ q ∈ (maskFreshPrimeMass (m := m) gap w).support,
        |g p q| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B * primeDivisorEta q (p.2 col)) →
      |expectation (maskStageOuterMass S hS gap C k w) (fun p =>
        b p * maskStageDensity S hS gap a C k U w p * expectation (maskFreshPrimeMass (m := m) gap w) (g p))| ^ 2 ≤
      (((2 ^ maskRowCountBound m : ℕ) : ℝ) + 1) *
        maskStageFreshOffDiagonalAverage S hS gap C k w (fun p pq =>
          maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2) + ε := by
  filter_upwards [maskRemoval_weighted_square_offDiagonal S hS gap a ha C hC hgap htail k U col B,
    (maskWeightedDiagonalLoss_tendsto_zero gap C hC hgap col B).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro b hbone g hg
  exact (hb b hbone g hg).trans (by linarith)

end Hindman168
