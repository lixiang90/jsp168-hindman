import Hindman168.MaskIntermediateMajorantMeans
import Hindman168.MaskGeneratedMonomialCertificates

/-! Actual original-law weighted-square prefactors for every finite
prefix of the multiplicative-mask iteration. Their invariant-row means
are derived on the unchanged master; the common cap depends only on m. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m : ℕ} (S : Finset (Fin (m + 1))) (hS : 2 ≤ S.card)

noncomputable def maskPrefixRowStage (k : ℕ) : TargetedMaskRowStage S :=
  (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate hS
    ((allNonemptyColumnMasks m).take k)

theorem maskPrefixRowStage_monomial (k : ℕ) :
    (maskPrefixRowStage S hS k).rows.MonomialStructure :=
  (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_monomial
    (initialTargetedMaskRowStage_monomial _ _) hS _

theorem maskPrefixRowStage_rowCount_le (k : ℕ) :
    (maskPrefixRowStage S hS k).rowCount ≤ maskRowCountBound m := by
  have h := (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).iterate_rowCount_le hS
    ((allNonemptyColumnMasks m).take k)
  calc
    _ ≤ 2 ^ ((allNonemptyColumnMasks m).take k).length *
      (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).rowCount := h
    _ ≤ 2 ^ (allNonemptyColumnMasks m).length *
      (initialTargetedMaskRowStage S (Finset.card_pos.mp (by omega))).rowCount := by
      gcongr
      · omega
      · simp only [List.length_take]
        exact Nat.min_le_right _ _
    _ = _ := by
      simp only [allNonemptyColumnMasks_length, initialTargetedMaskRowStage,
        nonemptyColumnSubset_card, maskRowCountBound]
      ring

noncomputable def maskStageInvariantRows (k : ℕ) (U : Finset (Fin (m + 1))) :
    Finset (Fin (maskPrefixRowStage S hS k).rowCount) :=
  Finset.univ.filter (fun i => maskRowInvariant ((maskPrefixRowStage S hS k).rows.row i)
    (chosenMaskColumnPlan S U hS).tag)

variable {N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskRemovalPrefactor (k : ℕ) (U : Finset (Fin (m + 1))) (w : ℕ) : ℝ :=
  monomialRestrictedMajorant gap a C (maskPrefixRowStage S hS k).rows
    (fun _ i => (maskPrefixRowStage S hS k).rows.normalizationAnchor i) (fun _ => id)
    (fun _ _ => True) (maskStageInvariantRows S hS k U) w

include ha hC hgap htail in
theorem maskRemovalPrefactor_tendsto (k : ℕ) (U : Finset (Fin (m + 1))) :
    Tendsto (maskRemovalPrefactor S hS gap a C k U) atTop
      (𝓝 (((2 ^ (maskStageInvariantRows S hS k U).card : ℕ) : ℝ))) := by
  let F := maskPrefixRowStage S hS k
  have ht := monomialRestrictedMajorant_tendsto_event gap a ha C hC F.rows
    (maskPrefixRowStage_monomial S hS k) F.target hgap htail
    (fun _ i => F.rows.normalizationAnchor i) (fun _ => id)
    (Eventually.of_forall (fun _ => Function.injective_id))
    (fun _ _ => True) (maskStageInvariantRows S hS k U)
  have hevent (w : ℕ) : event (monomialRowPrimeMass m gap F.primeArity w) (fun _ => True) = 1 := by
    have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
    simpa only [monomialRowPrimeMass, event, total, if_true] using hF.prime_slots_total w
      (fun _ : Fin F.primeArity => (gap w).val)
  have hz : Tendsto (fun w => maskRemovalPrefactor S hS gap a C k U w -
      (((2 ^ (maskStageInvariantRows S hS k U).card : ℕ) : ℝ))) atTop (𝓝 0) := by
    exact ht.congr (fun w => by rw [hevent, mul_one]; rfl)
  have h := hz.add (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
    (((2 ^ (maskStageInvariantRows S hS k U).card : ℕ) : ℝ))) atTop (𝓝 _))
  simpa only [sub_add_cancel, zero_add] using h

include ha hC hgap htail in
theorem maskRemovalPrefactor_eventually_cap (k : ℕ) (U : Finset (Fin (m + 1))) :
    ∀ᶠ w in atTop, maskRemovalPrefactor S hS gap a C k U w ≤
      (((2 ^ maskRowCountBound m : ℕ) : ℝ)) + 1 := by
  have hc : (maskStageInvariantRows S hS k U).card ≤ maskRowCountBound m :=
    (Finset.card_le_univ _).trans (by simpa using maskPrefixRowStage_rowCount_le S hS k)
  have hp : (((2 ^ (maskStageInvariantRows S hS k U).card : ℕ) : ℝ)) ≤
      (((2 ^ maskRowCountBound m : ℕ) : ℝ)) := by
    exact_mod_cast (show (2 : ℕ) ^ (maskStageInvariantRows S hS k U).card ≤ 2 ^ maskRowCountBound m by
      gcongr; omega)
  exact ((maskRemovalPrefactor_tendsto S hS gap a ha C hC hgap htail k U).eventually
    (eventually_lt_nhds (lt_add_one _))).mono (fun _ hw => by linarith)

include ha hC hgap htail in
theorem maskRemovalPrefactors_eventually_cap :
    ∀ᶠ w in atTop, ∀ k : Fin ((allNonemptyColumnMasks m).length + 1),
      ∀ U : Finset (Fin (m + 1)), maskRemovalPrefactor S hS gap a C k.val U w ≤
        (((2 ^ maskRowCountBound m : ℕ) : ℝ)) + 1 := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro U
  exact maskRemovalPrefactor_eventually_cap S hS gap a ha C hC hgap htail k.val U

end Hindman168
