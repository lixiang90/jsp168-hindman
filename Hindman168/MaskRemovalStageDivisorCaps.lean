import Hindman168.MaskRemovalStageDiagonal
import Hindman168.PredictionDivisorSupBounds

/-! Polynomial sup bounds for the actual intermediate row density.
The original tail budget is at the earlier gap, not the larger pivot
auxiliary value. These bounds let the weighted square use diagonal
error estimates with a fixed exponent depending only on m. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)
  (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskStageRowWeight_eventually_bounds :
    ∀ᶠ w in atTop, ∀ k i x z,
      0 ≤ monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z ∧
      monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
        (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i x z ≤
          (maskGeneratedMaster m gap).auxiliary w (gap w).val := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid, htail] with w hw ht
  intro k i x z
  let col := (maskPrefixRowStage S hS k).rows.normalizationAnchor i
  let Xs := (C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col
  have hv : ValidCutoffs Xs (primorial w) := chain_tailCutoffs_valid (C w)
    ((maskGeneratedMaster m gap).cutoff w) (primorial w) (hC w)
    (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) col
  have hb := hF.chain_tail_budget_at_gap (C w) w col (gap w).val (ht col)
  exact integerDivisorMask_probability_bounds (tailMass (primorial w) Xs)
    ((maskGeneratedMaster m gap).auxiliary w (gap w).val)
    (tailMass_nonneg (primorial_pos w) Xs hv) (tailMass_total (primorial_pos w) Xs hv)
    (fun q hq => ((tailMass_support Xs hv q hq).2.1).trans hb) _

include hC htail in
theorem maskStageDensity_eventually_polynomial_cap :
    ∀ᶠ w in atTop, ∀ k U p, maskStageDensity S hS gap a C k U w p ≤
      ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m) := by
  filter_upwards [maskStageRowWeight_eventually_bounds S hS gap a C hC htail] with w hw
  intro k U p
  let V : ℝ := (maskGeneratedMaster m gap).auxiliary w (gap w).val
  have hV : 2 ≤ V := by
    dsimp [V]
    exact_mod_cast (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
  have hc : (maskStageInvariantRows S hS k U).card ≤ maskRowCountBound m :=
    (Finset.card_le_univ _).trans (by simpa using maskPrefixRowStage_rowCount_le S hS k)
  unfold maskStageDensity
  calc
    _ ≤ ∏ i ∈ maskStageInvariantRows S hS k U, V ^ 2 := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg zero_le_one (hw k i p.1 p.2).1
      · intro i _
        have hi := (hw k i p.1 p.2).2
        change monomialRowWeight gap a C (maskPrefixRowStage S hS k).rows
          (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i p.1 p.2 ≤ V at hi
        nlinarith
    _ = V ^ (2 * (maskStageInvariantRows S hS k U).card) := by rw [Finset.prod_const, ← pow_mul]
    _ ≤ V ^ (2 * maskRowCountBound m) := pow_le_pow_right₀ (by linarith) (by omega)

include hC htail in
theorem maskStageWeightedDouble_integrand_bound (k : ℕ) (U : Finset (Fin (m + 1)))
    (col : Fin (m + 1)) (B : ℕ) :
    ∀ᶠ w in atTop, ∀ g : MaskStagePoint S hS k → ℕ → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ q ∈ (maskFreshPrimeMass (m := m) gap w).support,
        |g p q| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ B * primeDivisorEta q (p.2 col)) →
      ∀ p ∈ (maskStageOuterMass S hS gap C k w).support,
        ∀ pq ∈ (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w)).support,
        |maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2| ≤
          ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^
            (2 * maskRowCountBound m + 2 * B) *
              (primeDivisorEta pq.1 (p.2 col) * primeDivisorEta pq.2 (p.2 col)) := by
  filter_upwards [maskStageDensity_eventually_nonneg S hS gap a C hC,
    maskStageDensity_eventually_polynomial_cap S hS gap a C hC htail] with w hn hc
  intro g hg p hp pq hpq
  have hpair := Finset.mem_product.mp (tensor_support _ _ hpq)
  have hprod := mul_le_mul (hg p hp pq.1 hpair.1) (hg p hp pq.2 hpair.2)
    (abs_nonneg _) (by positivity [primeDivisorEta_nonneg pq.1 (p.2 col)])
  have htotal := mul_le_mul (hc k U p) hprod (by positivity)
    (by positivity : (0 : ℝ) ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ (2 * maskRowCountBound m))
  rw [abs_mul, abs_mul, abs_of_nonneg (hn k U p)]
  calc
    _ = maskStageDensity S hS gap a C k U w p * (|g p pq.1| * |g p pq.2|) := by ring
    _ ≤ _ := htotal
    _ = _ := by rw [pow_add, pow_mul, pow_two]; ring

end Hindman168
