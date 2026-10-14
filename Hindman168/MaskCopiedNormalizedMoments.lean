import Hindman168.MaskCopiedStagePrefactors
import Hindman168.FiniteReplicaConditioning

/-! Normalization uses the actual generated good-prime event, whose mass
is proved to tend to one by the fixed master catalogue inclusion. Copied
means and stage-prefactor bounds consequently hold under its original
conditional probability law; no positive-mass or mean-limit premise is
supplied in these applications. -/

set_option maxHeartbeats 2000000

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem maskGeneratedCopiedGood_event_tendsto_one (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    Tendsto (fun w => event (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
      (maskGeneratedCopiedPrimeGood m gap t w)) atTop (𝓝 1) := by
  let T := maskGeneratedRowDataFamily m gap t
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have he (w : ℕ) : event (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
      (maskGeneratedCopiedPrimeGood m gap t w) =
      event (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
        (predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
          (T.rows.catalog T.target) (T.rows.denominator T.target) w) := by
    rw [← expectation_indicator, ← expectation_indicator]
    apply expectation_congr_support
    intro x hx
    simp only [maskGeneratedCopiedPrimeGood, hx, true_and, T]
  simp_rw [he]
  exact hF.local_prime_good_event_tendsto_one (T.rows.catalog T.target) (T.rows.denominator T.target)
    (T.rows.denominator_mem_catalog T.target) T.slot T.slot_injective
    (fun f hf => originalRowMasterCatalog_inclusion (maskGeneratedRowDataFamily m gap) t f hf) gap

namespace MaskCopiedSampling

variable {m N : ℕ}

theorem conditioned_prime_probability_eventually (S : MaskCopiedSampling m N) :
    ∀ᶠ w in atTop,
      (∀ x, 0 ≤ conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w) x) ∧
      total (conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w)) = 1 := by
  have hF := maskGeneratedMaster_conditions m S.gap (∅ : Finset ℚ) (by simp)
  filter_upwards [(maskGeneratedCopiedGood_event_tendsto_one m S.gap S.template).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
  exact ⟨conditionMass_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (S.gap w).val)),
    conditionMass_total _ _ hw⟩

noncomputable def normalizedMajorant (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (U : Finset (Fin q)) (w : ℕ) : ℝ :=
  expectation (conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
    (fun x => expectation (S.baseMass w x) (fun y => ∏ u ∈ U, (1 + S.weight label row w u x y)))

theorem normalizedMajorant_eq (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (U : Finset (Fin q)) (w : ℕ) :
    S.normalizedMajorant label row U w =
      conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
        (maskGeneratedCopiedPrimeGood m S.gap S.template w)
        (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) /
          event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w) := by
  unfold normalizedMajorant
  rw [expectation_conditionMass]
  rfl

theorem normalizedMajorant_tendsto (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    Tendsto (S.normalizedMajorant label row U) atTop (𝓝 (((2 ^ U.card : ℕ) : ℝ))) := by
  have hp : Tendsto (fun w => event (S.primeMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)) atTop (𝓝 1) :=
    maskGeneratedCopiedGood_event_tendsto_one m S.gap S.template
  have hm := S.majorant_mean_tendsto label row hrow hdivbudget U
  have hn := hm.add ((tendsto_const_nhds (x := ((2 ^ U.card : ℕ) : ℝ))).mul hp)
  simp only [sub_add_cancel, mul_one, zero_add] at hn
  have hd := hn.div hp (by norm_num : (1 : ℝ) ≠ 0)
  have he := hd.congr (fun w => (S.normalizedMajorant_eq label row U w).symm)
  simpa only [div_one] using he

theorem normalizedMajorant_eventually_le_column_bound (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    ∀ᶠ w in atTop, S.normalizedMajorant label row U w ≤ maskCopiedMajorantBound m := by
  have hq : q ≤ Fintype.card (MaskCopiedRow m S.gap S.template) := by
    obtain ⟨w, hw⟩ := hrow.exists
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (row w) hw
  have hU : U.card ≤ (maskRowCountBound m + 1) * 2 ^ maskRowCountBound m :=
    (Finset.card_le_univ U).trans (by
      simpa only [Fintype.card_fin] using hq.trans (maskCopiedRow_card_le m S.gap S.template))
  filter_upwards [(S.normalizedMajorant_tendsto label row hrow hdivbudget U).eventually
    (Iio_mem_nhds (by linarith : ((2 ^ U.card : ℕ) : ℝ) < ((2 ^ U.card : ℕ) : ℝ) + 1))] with w hw
  exact hw.le.trans (by unfold maskCopiedMajorantBound; gcongr; norm_num)

noncomputable def normalizedStagePrefactor (S : MaskCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1)) (w : ℕ) (K : Finset S.Direction) (base : S.BaseRow) : ℝ :=
  expectation (conditionMass (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
    (fun x => expectation (piMass (S.originalColumnMass w x)) (fun z =>
      expectation (piMass (fun k => tensor (S.directionMass w x k) (S.directionMass w x k)))
        (fun v => ∏ u ∈ S.stageIndices K base,
          (1 + S.weight (S.labels label) S.rows w u x (additiveSampleCoordinates z v)))))

theorem normalizedStagePrefactor_eq (S : MaskCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1)) (w : ℕ) (K : Finset S.Direction) (base : S.BaseRow) :
    S.normalizedStagePrefactor label w K base = S.stagePrefactor label w K base /
      event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w) := by
  unfold normalizedStagePrefactor
  rw [expectation_conditionMass]
  rfl

theorem normalizedStagePrefactor_eventually_le (S : MaskCopiedSampling m N)
    (label : ℕ → S.BaseRow → Fin (m + 1))
    (hdivbudget : ∀ᶠ w in atTop, ∀ base,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w base)) ≤ S.budget w)
    (haux : ∀ k bit, S.columnIndex (.inr (k, bit)) ∉ S.harmonic)
    (hloc : ∀ w x k bit, S.location w x (S.columnIndex (.inr (k, bit))) =
      S.location w x (S.columnIndex (.inr (k, false))))
    (hlen : ∀ w x k bit, S.length w x (S.columnIndex (.inr (k, bit))) =
      S.length w x (S.columnIndex (.inr (k, false))))
    (K : Finset S.Direction) (base : S.BaseRow) :
    ∀ᶠ w in atTop, S.normalizedStagePrefactor label w K base ≤ maskCopiedMajorantBound m := by
  have h := S.normalizedMajorant_eventually_le_column_bound (S.labels label) S.rows
    (Eventually.of_forall (fun _ => (Fintype.equivFin (MaskCopiedRow m S.gap S.template)).symm.injective))
    (hdivbudget.mono (fun w hw u => hw (S.rows w u).val.1)) (S.stageIndices K base)
  simpa only [S.normalizedStagePrefactor_eq, S.stagePrefactor_eq label haux hloc hlen,
    S.normalizedMajorant_eq] using h

end MaskCopiedSampling
end Hindman168
