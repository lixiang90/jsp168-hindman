import Hindman168.MaskRawCorrelationTransfer

/-! The full original base-row majorant has its actual mean 2^q under
the unconditioned prime and harmonic laws. Consequently raw and good-event
conditioned source correlations have uniform constant caps. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))

noncomputable def originalMajorantMeanConstant : ℝ :=
  ((2 ^ Fintype.card (MaskOriginalBaseRow m gap t) : ℕ) : ℝ)

noncomputable def originalFullMajorantMass (w : ℕ) : ℝ :=
  expectation (basePrimeMass gap t w) (fun x => expectation (maskOriginalBaseMass m gap C w)
    (originalMajorantProduct gap a C t label w x))

theorem originalFullMajorantMass_eq_enumerated (w : ℕ) :
    originalFullMajorantMass gap a C t label w =
      baseRestrictedMajorant gap a C t (originalLabelEnumeration gap t label)
        (originalRowEnumeration gap t) (fun _ _ => True) Finset.univ w := by
  simpa only [originalFullMajorantMass, conditionalFiniteAverage, if_true] using
    originalRestrictedMajorant_eq_enumerated gap a C t label (fun _ _ => True) w

include ha hC in
theorem originalFullMajorantMass_tendsto
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    Tendsto (originalFullMajorantMass gap a C t label) atTop
      (𝓝 (originalMajorantMeanConstant gap t)) := by
  have hevent (w : ℕ) : event (basePrimeMass gap t w) (fun _ => True) = 1 := by
    simpa only [event, total, if_true] using (basePrime_probability gap t w).2
  have ht := baseRestrictedMajorant_tendsto_event gap a ha C hC t hgap htail
    (originalLabelEnumeration gap t label) (originalRowEnumeration gap t)
    (Eventually.of_forall (originalRowEnumeration_injective gap t)) (fun _ _ => True) Finset.univ
  have hz : Tendsto (fun w => originalFullMajorantMass gap a C t label w -
      originalMajorantMeanConstant gap t) atTop (𝓝 0) := by
    exact ht.congr (fun w => by
      rw [← originalFullMajorantMass_eq_enumerated, hevent]
      simp only [Finset.card_univ, Fintype.card_fin, mul_one, originalMajorantMeanConstant])
  have h := hz.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => originalMajorantMeanConstant gap t)
    atTop (𝓝 (originalMajorantMeanConstant gap t)))
  simpa only [sub_add_cancel, zero_add] using h

include hC in
theorem rawCorrelation_full_majorant_bound :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |rawCorrelation gap a C t (fun _ => F) w| ≤ originalFullMajorantMass gap a C t label w := by
  filter_upwards [base_probability_eventually gap C hC] with w hb
  intro F hF
  apply abs_expectation_le_majorant_support _ _ _ (basePrime_probability gap t w).1
  intro x hx
  apply abs_expectation_le_majorant_support _ _ _ hb.1
  intro z _
  exact originalProduct_majorant_bound gap a C t label (fun _ => F) w x (hF x hx) z

include hC in
theorem original_good_restricted_full_majorant_bound :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
        (maskGeneratedCopiedPrimeGood m gap t w) (originalProduct gap a C t (fun _ => F) w)| ≤
        originalFullMajorantMass gap a C t label w := by
  filter_upwards [base_probability_eventually gap C hC, rowMajorant_eventually_nonneg gap C hC t label]
    with w hb hm
  intro F hF
  apply abs_expectation_le_majorant_support _ _ _ (basePrime_probability gap t w).1
  intro x hx
  have hnonneg : 0 ≤ expectation (maskOriginalBaseMass m gap C w)
      (originalMajorantProduct gap a C t label w x) :=
    expectation_nonneg _ _ hb.1 (fun _ => Finset.prod_nonneg (fun base _ => hm base _))
  by_cases hg : maskGeneratedCopiedPrimeGood m gap t w x
  · simp only [if_pos hg]
    apply abs_expectation_le_majorant_support _ _ _ hb.1
    intro z _
    exact originalProduct_majorant_bound gap a C t label (fun _ => F) w x (hF x hx) z
  · simpa only [if_neg hg, abs_zero] using hnonneg

include ha hC in
theorem source_correlations_constant_caps (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |rawCorrelation gap a C t (fun _ => F) w| ≤ originalMajorantMeanConstant gap t + 1 ∧
      |unshiftedCorrelation gap a ha C hC t J hJ hgap (fun _ => F) w| ≤
        2 * (originalMajorantMeanConstant gap t + 1) := by
  filter_upwards [rawCorrelation_full_majorant_bound gap a C hC t label,
    original_good_restricted_full_majorant_bound gap a C hC t label,
    (originalFullMajorantMass_tendsto gap a ha C hC t label hgap htail).eventually
      (eventually_lt_nhds (lt_add_one _)),
    (baseGoodPrimeMass_tendsto_one gap t).eventually
      (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with w hr hg hm hp
  intro F hF
  refine ⟨(hr F hF).trans hm.le, ?_⟩
  rw [conditionedCorrelation_eq_restricted_div, abs_div, abs_of_pos (by linarith :
    0 < event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w))]
  apply (div_le_iff₀ (by linarith :
    0 < event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w))).mpr
  have hK : 0 ≤ originalMajorantMeanConstant gap t := Nat.cast_nonneg _
  have hh := (hg F hF).trans hm.le
  nlinarith

end Hindman168.MaskOriginalSampling
