import Hindman168.MaskBaseRestrictedMean
import Hindman168.PredictionCopiedCancellation
import Hindman168.UniformAdmissibleInputLimit

/-! Restricted-domain majorant means for distinct actual base rows.
Uniformity is over every prime-only event, preserving the original laws.
An event of vanishing probability has vanishing full majorant mass. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N q : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → Fin q → Fin (m + 1))
  (row : ℕ → Fin q → Fin (maskGeneratedRowDataFamily m gap t).rowCount)
  (hrow : ∀ᶠ w in atTop, Function.Injective (row w))

noncomputable def baseRestrictedMajorant
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop)
    (U : Finset (Fin q)) (w : ℕ) : ℝ :=
  conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
    (E w) (fun x z => ∏ u ∈ U, (1 + baseRowWeight gap a C t label row w u x z))

theorem base_subset_average_eq
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop)
    (U : Finset (Fin q)) (w : ℕ) :
    conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
      (E w) (fun x z => ∏ u ∈ U, baseRowWeight gap a C t label row w u x z) =
      baseRestrictedMean gap a C t
        (fun w u => label w ((Fintype.equivFin U).symm u).val)
        (fun w u => row w ((Fintype.equivFin U).symm u).val) E w := by
  unfold conditionalFiniteAverage baseRestrictedMean
  apply congrArg (expectation (basePrimeMass gap t w))
  funext x
  split_ifs
  · apply congrArg (expectation (maskOriginalBaseMass m gap C w))
    funext z
    exact (finset_product_fin_equiv U (fun u => baseRowWeight gap a C t label row w u x z)).symm
  · rfl

include ha hC hgap htail hrow in
theorem base_subset_mean_tendsto_event
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage (basePrimeMass gap t w)
      (fun _ => maskOriginalBaseMass m gap C w) (E w)
      (fun x z => ∏ u ∈ U, baseRowWeight gap a C t label row w u x z) -
        event (basePrimeMass gap t w) (E w)) atTop (𝓝 0) := by
  simp_rw [base_subset_average_eq]
  apply baseRestrictedMean_tendsto_event gap a ha C hC t hgap htail
  exact hrow.mono (fun _ hw => hw.comp (Subtype.val_injective.comp (Fintype.equivFin U).symm.injective))

include ha hC hgap htail hrow in
theorem baseRestrictedMajorant_tendsto_event
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop)
    (U : Finset (Fin q)) :
    Tendsto (fun w => baseRestrictedMajorant gap a C t label row E U w -
      ((2 ^ U.card : ℕ) : ℝ) * event (basePrimeMass gap t w) (E w)) atTop (𝓝 0) := by
  apply retained_majorant_average_mean_one (basePrimeMass gap t)
    (fun w _ => maskOriginalBaseMass m gap C w) E (baseRowWeight gap a C t label row) U
    (fun w => event (basePrimeMass gap t w) (E w))
  intro S _
  exact base_subset_mean_tendsto_event gap a ha C hC t hgap htail label row hrow E S

include ha hC hgap htail hrow in
theorem baseRestrictedMajorant_uniform_event_error (U : Finset (Fin q)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ E : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop,
      |baseRestrictedMajorant gap a C t label row (fun _ => E) U w -
        ((2 ^ U.card : ℕ) : ℝ) * event (basePrimeMass gap t w) E| < ε := by
  have h := uniform_zero_of_admissible_sequences
    (fun _ (_ : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop) => True)
    (fun w E => baseRestrictedMajorant gap a C t label row (fun _ => E) U w -
      ((2 ^ U.card : ℕ) : ℝ) * event (basePrimeMass gap t w) E)
    (fun _ _ => False) (Eventually.of_forall (fun _ => True.intro))
    (by
      intro E _
      have ht := baseRestrictedMajorant_tendsto_event gap a ha C hC t hgap htail label row hrow E U
      exact ht.congr (fun _ => rfl))
  intro ε hε
  exact (h ε hε).mono (fun _ hw E => hw E True.intro)

include ha hC hgap htail hrow in
theorem baseRestrictedMajorant_tendsto_zero
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop)
    (hE : Tendsto (fun w => event (basePrimeMass gap t w) (E w)) atTop (𝓝 0))
    (U : Finset (Fin q)) :
    Tendsto (baseRestrictedMajorant gap a C t label row E U) atTop (𝓝 0) := by
  have ht := (baseRestrictedMajorant_tendsto_event gap a ha C hC t hgap htail label row hrow E U).add
    (hE.const_mul ((2 ^ U.card : ℕ) : ℝ))
  simpa only [sub_add_cancel, mul_zero, add_zero] using ht

end Hindman168.MaskOriginalSampling
