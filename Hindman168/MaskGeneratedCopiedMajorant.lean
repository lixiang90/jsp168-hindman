import Hindman168.MaskGeneratedCopiedMeanOne
import Hindman168.PredictionCopiedCancellation

/-! Subset expansion gives the actual general copied-row majorant mean and
an eventual bound from the original varying prime-only event probability. -/

namespace Hindman168.MaskCopiedSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ}

noncomputable def weight (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (w : ℕ) (u : Fin q) (x : Fin (maskGeneratedRowDataFamily m S.gap S.template).arity → ℕ)
    (y : MaskCopiedIndex m S.gap S.template → ℤ) : ℝ :=
  integerDivisorMask (tailMass (primorial w)
    ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)))
    (∑ j, S.coefficient row w x u j * y j)

theorem subset_average_eq (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (U : Finset (Fin q)) (w : ℕ) :
    conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ U, S.weight label row w u x y) =
    S.mean (fun w u => label w ((Fintype.equivFin U).symm u).val)
      (fun w u => row w ((Fintype.equivFin U).symm u).val) w := by
  unfold conditionalFiniteAverage mean masterChainWeightedMean
  congr 1
  funext x
  split_ifs
  · congr 1
    funext y
    exact (finset_product_fin_equiv U (fun u => S.weight label row w u x y)).symm
  · rfl

set_option maxHeartbeats 1000000 in
theorem subset_mean_one_tendsto (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ U, S.weight label row w u x y) -
        event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w)) atTop (𝓝 0) := by
  simp_rw [S.subset_average_eq label row U]
  apply S.mean_one_tendsto
  · exact hrow.mono (fun w hr => hr.comp
      (Subtype.val_injective.comp (Fintype.equivFin U).symm.injective))
  · exact hdivbudget.mono (fun w hw u => hw ((Fintype.equivFin U).symm u).val)

set_option maxHeartbeats 1000000 in
theorem majorant_mean_tendsto (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) -
        ((2 ^ U.card : ℕ) : ℝ) * event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
      atTop (𝓝 0) := by
  apply retained_majorant_average_mean_one (fun w => S.primeMass w) S.baseMass
    (maskGeneratedCopiedPrimeGood m S.gap S.template) (S.weight label row) U
    (fun w => event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
  intro T _
  exact S.subset_mean_one_tendsto label row hrow hdivbudget T

set_option maxHeartbeats 1000000 in
theorem majorant_eventually_le (S : MaskCopiedSampling m N) {q : ℕ}
    (label : ℕ → Fin q → Fin (m + 1)) (row : ℕ → Fin q → MaskCopiedRow m S.gap S.template)
    (hrow : ∀ᶠ w in atTop, Function.Injective (row w))
    (hdivbudget : ∀ᶠ w in atTop, ∀ u,
      tailBound ((S.chain w).tailCutoffs ((maskGeneratedMaster m S.gap).cutoff w) (label w u)) ≤ S.budget w)
    (U : Finset (Fin q)) :
    ∀ᶠ w in atTop, conditionalFiniteAverage (S.primeMass w) (S.baseMass w)
      (maskGeneratedCopiedPrimeGood m S.gap S.template w)
      (fun x y => ∏ u ∈ U, (1 + S.weight label row w u x y)) ≤ ((2 ^ U.card : ℕ) : ℝ) + 1 := by
  apply varying_event_mean_eventually_le
    (k := fun w => event (S.primeMass w) (maskGeneratedCopiedPrimeGood m S.gap S.template w))
    ((2 ^ U.card : ℕ) : ℝ) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro w
    have hA : ∀ a ∈ Finset.univ.image S.a, 0 < a := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact S.positive j
    have hF := maskGeneratedMaster_conditions m S.gap (Finset.univ.image S.a) hA
    exact (event_le_total (S.primeMass w) _ (hF.prime_slots_nonneg w (fun _ => (S.gap w).val))).trans_eq
      (hF.prime_slots_total w (fun _ => (S.gap w).val))
  · exact S.majorant_mean_tendsto label row hrow hdivbudget U

end Hindman168.MaskCopiedSampling
