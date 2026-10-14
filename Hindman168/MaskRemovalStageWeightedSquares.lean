import Hindman168.MaskRemovalStagePrefactors
import Hindman168.FiniteConditionalJoint
import Hindman168.MaskOriginalStagePrefactors

/-! Weighted squaring on each actual intermediate row/prime/base law.
The old prime tuple is shared, while the two new pool primes are sampled
independently. The invariant-row prefactor has a derived m-only cap.
The prime-insertion and branch-absorption identities are separate work. -/

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

abbrev MaskStagePoint (k : ℕ) :=
  (Fin (maskPrefixRowStage S hS k).primeArity → ℕ) × (Fin (m + 1) → ℤ)

noncomputable def maskStageOuterMass (k w : ℕ) : Mass (MaskStagePoint S hS k) :=
  conditionalJoint (monomialRowPrimeMass m gap (maskPrefixRowStage S hS k).primeArity w)
    (fun _ => maskOriginalBaseMass m gap C w)

noncomputable def maskStageDensity (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ)
    (p : MaskStagePoint S hS k) : ℝ :=
  ∏ i ∈ maskStageInvariantRows S hS k U, (1 + monomialRowWeight gap a C
    (maskPrefixRowStage S hS k).rows
    (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id) w i p.1 p.2)

noncomputable def maskFreshPrimeMass (w : ℕ) : Mass ℕ :=
  primePoolMass ((maskGeneratedMaster m gap).pool w (gap w).val).lower
    ((maskGeneratedMaster m gap).pool w (gap w).val).upper

theorem maskStageDensity_average (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ) :
    expectation (maskStageOuterMass S hS gap C k w) (maskStageDensity S hS gap a C k U w) =
      maskRemovalPrefactor S hS gap a C k U w := by
  rw [maskStageOuterMass, expectation_conditionalJoint]
  unfold maskRemovalPrefactor monomialRestrictedMajorant conditionalFiniteAverage
  simp only [if_true]
  rfl

include hC in
theorem maskStageOuterMass_eventually_nonneg :
    ∀ᶠ w in atTop, ∀ k p, 0 ≤ maskStageOuterMass S hS gap C k w p := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [base_probability_eventually gap C hC] with w hb
  intro k p
  exact conditionalJoint_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (gap w).val))
    (fun _ _ => hb.1) p

include hC in
theorem maskStageDensity_eventually_nonneg :
    ∀ᶠ w in atTop, ∀ k U p, 0 ≤ maskStageDensity S hS gap a C k U w p := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro k U p
  apply Finset.prod_nonneg
  intro i _
  have hv := chain_tailCutoffs_valid (C w) ((maskGeneratedMaster m gap).cutoff w)
    (primorial w) (hC w) (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩)
    ((maskPrefixRowStage S hS k).rows.normalizationAnchor i)
  exact add_nonneg zero_le_one (expectation_nonneg _ _
    (tailMass_nonneg (primorial_pos w) _ hv) (fun _ => by split_ifs <;> positivity))

include hC in
theorem maskRemoval_weighted_square_eventually (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop,
    ∀ b : MaskStagePoint S hS k → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support, |b p| ≤ 1) →
    ∀ g : MaskStagePoint S hS k → ℕ → ℝ,
      |expectation (maskStageOuterMass S hS gap C k w) (fun p =>
        b p * maskStageDensity S hS gap a C k U w p * expectation (maskFreshPrimeMass (m := m) gap w) (g p))| ^ 2 ≤
      maskRemovalPrefactor S hS gap a C k U w *
        expectation (maskStageOuterMass S hS gap C k w) (fun p =>
          expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
            (fun pq => maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2)) := by
  filter_upwards [maskStageOuterMass_eventually_nonneg S hS gap C hC,
    maskStageDensity_eventually_nonneg S hS gap a C hC] with w hμ hΩ
  intro b hb g
  have hcs := conditional_weighted_cauchy_schwarz (maskStageOuterMass S hS gap C k w) (hμ k)
    (fun _ => maskFreshPrimeMass (m := m) gap w)
    (fun p => b p * maskStageDensity S hS gap a C k U w p)
    (maskStageDensity S hS gap a C k U w) g
    (fun p hp => by
      rw [abs_mul, abs_of_nonneg (hΩ k U p)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb p hp) (hΩ k U p))
  rw [maskStageDensity_average] at hcs
  exact hcs

include ha hC hgap htail in
theorem maskRemoval_weighted_square_constant_cap (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop,
    ∀ b : MaskStagePoint S hS k → ℝ,
      (∀ p ∈ (maskStageOuterMass S hS gap C k w).support, |b p| ≤ 1) →
    ∀ g : MaskStagePoint S hS k → ℕ → ℝ,
      |expectation (maskStageOuterMass S hS gap C k w) (fun p =>
        b p * maskStageDensity S hS gap a C k U w p * expectation (maskFreshPrimeMass (m := m) gap w) (g p))| ^ 2 ≤
      ((((2 ^ maskRowCountBound m : ℕ) : ℝ)) + 1) *
        expectation (maskStageOuterMass S hS gap C k w) (fun p =>
          expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
            (fun pq => maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2)) := by
  filter_upwards [maskRemoval_weighted_square_eventually S hS gap a C hC k U,
    maskRemovalPrefactor_eventually_cap S hS gap a ha C hC hgap htail k U,
    maskStageOuterMass_eventually_nonneg S hS gap C hC,
    maskStageDensity_eventually_nonneg S hS gap a C hC] with w hs hc hμ hΩ
  intro b hb g
  have hnonneg : 0 ≤ expectation (maskStageOuterMass S hS gap C k w) (fun p =>
      expectation (tensor (maskFreshPrimeMass (m := m) gap w) (maskFreshPrimeMass (m := m) gap w))
        (fun pq => maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2)) := by
    apply expectation_nonneg _ _ (hμ k)
    intro p
    have he : (fun pq : ℕ × ℕ => maskStageDensity S hS gap a C k U w p * g p pq.1 * g p pq.2) =
        fun pq => maskStageDensity S hS gap a C k U w p * (g p pq.1 * g p pq.2) := by
      funext pq
      ring
    rw [he, expectation_const_mul, expectation_independent_square]
    exact mul_nonneg (hΩ k U p) (sq_nonneg _)
  exact (hs b hb g).trans (mul_le_mul_of_nonneg_right hc hnonneg)

end Hindman168
