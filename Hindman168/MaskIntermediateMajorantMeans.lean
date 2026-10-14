import Hindman168.MaskIntermediateRestrictedMean
import Hindman168.PredictionCopiedCancellation
import Hindman168.UniformAdmissibleInputLimit

/-! Restricted and full majorant means for every fixed monomial row
family, including intermediate mask-removal stages. The actual original
prime and harmonic laws are preserved on every varying prime-only domain. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N n r q : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
  (hmono : F.MonomialStructure) (target : Fin r)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → Fin q → Fin (m + 1))
  (row : ℕ → Fin q → Fin r)
  (hrow : ∀ᶠ w in atTop, Function.Injective (row w))

noncomputable def monomialRestrictedMajorant
    (E : ℕ → (Fin n → ℕ) → Prop)
    (U : Finset (Fin q)) (w : ℕ) : ℝ :=
  conditionalFiniteAverage (monomialRowPrimeMass m gap n w) (fun _ => maskOriginalBaseMass m gap C w)
    (E w) (fun x z => ∏ u ∈ U, (1 + monomialRowWeight gap a C F label row w u x z))

theorem monomial_subset_average_eq
    (E : ℕ → (Fin n → ℕ) → Prop)
    (U : Finset (Fin q)) (w : ℕ) :
    conditionalFiniteAverage (monomialRowPrimeMass m gap n w) (fun _ => maskOriginalBaseMass m gap C w)
      (E w) (fun x z => ∏ u ∈ U, monomialRowWeight gap a C F label row w u x z) =
      monomialRestrictedMean gap a C F
        (fun w u => label w ((Fintype.equivFin U).symm u).val)
        (fun w u => row w ((Fintype.equivFin U).symm u).val) E w := by
  unfold conditionalFiniteAverage monomialRestrictedMean
  apply congrArg (expectation (monomialRowPrimeMass m gap n w))
  funext x
  split_ifs
  · apply congrArg (expectation (maskOriginalBaseMass m gap C w))
    funext z
    exact (finset_product_fin_equiv U (fun u => monomialRowWeight gap a C F label row w u x z)).symm
  · rfl

include ha hC hmono target hgap htail hrow in
theorem monomial_subset_mean_tendsto_event
    (E : ℕ → (Fin n → ℕ) → Prop)
    (U : Finset (Fin q)) :
    Tendsto (fun w => conditionalFiniteAverage (monomialRowPrimeMass m gap n w)
      (fun _ => maskOriginalBaseMass m gap C w) (E w)
      (fun x z => ∏ u ∈ U, monomialRowWeight gap a C F label row w u x z) -
        event (monomialRowPrimeMass m gap n w) (E w)) atTop (𝓝 0) := by
  simp_rw [monomial_subset_average_eq]
  apply monomialRestrictedMean_tendsto_event gap a ha C hC F hmono target hgap htail
  exact hrow.mono (fun _ hw => hw.comp (Subtype.val_injective.comp (Fintype.equivFin U).symm.injective))

include ha hC hmono target hgap htail hrow in
theorem monomialRestrictedMajorant_tendsto_event
    (E : ℕ → (Fin n → ℕ) → Prop)
    (U : Finset (Fin q)) :
    Tendsto (fun w => monomialRestrictedMajorant gap a C F label row E U w -
      ((2 ^ U.card : ℕ) : ℝ) * event (monomialRowPrimeMass m gap n w) (E w)) atTop (𝓝 0) := by
  apply retained_majorant_average_mean_one (monomialRowPrimeMass m gap n)
    (fun w _ => maskOriginalBaseMass m gap C w) E (monomialRowWeight gap a C F label row) U
    (fun w => event (monomialRowPrimeMass m gap n w) (E w))
  intro S _
  exact monomial_subset_mean_tendsto_event gap a ha C hC F hmono target hgap htail label row hrow E S

include ha hC hmono target hgap htail hrow in
theorem monomialRestrictedMajorant_uniform_event_error (U : Finset (Fin q)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ E : (Fin n → ℕ) → Prop,
      |monomialRestrictedMajorant gap a C F label row (fun _ => E) U w -
        ((2 ^ U.card : ℕ) : ℝ) * event (monomialRowPrimeMass m gap n w) E| < ε := by
  have h := uniform_zero_of_admissible_sequences
    (fun _ (_ : (Fin n → ℕ) → Prop) => True)
    (fun w E => monomialRestrictedMajorant gap a C F label row (fun _ => E) U w -
      ((2 ^ U.card : ℕ) : ℝ) * event (monomialRowPrimeMass m gap n w) E)
    (fun _ _ => False) (Eventually.of_forall (fun _ => True.intro))
    (by
      intro E _
      have ht := monomialRestrictedMajorant_tendsto_event gap a ha C hC F hmono target hgap htail label row hrow E U
      exact ht.congr (fun _ => rfl))
  intro ε hε
  exact (h ε hε).mono (fun _ hw E => hw E True.intro)

include ha hC hmono target hgap htail hrow in
theorem monomialRestrictedMajorant_tendsto_zero
    (E : ℕ → (Fin n → ℕ) → Prop)
    (hE : Tendsto (fun w => event (monomialRowPrimeMass m gap n w) (E w)) atTop (𝓝 0))
    (U : Finset (Fin q)) :
    Tendsto (monomialRestrictedMajorant gap a C F label row E U) atTop (𝓝 0) := by
  have ht := (monomialRestrictedMajorant_tendsto_event gap a ha C hC F hmono target hgap htail label row hrow E U).add
    (hE.const_mul ((2 ^ U.card : ℕ) : ℝ))
  simpa only [sub_add_cancel, mul_zero, add_zero] using ht

end Hindman168.MaskOriginalSampling
