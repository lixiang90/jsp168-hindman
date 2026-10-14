import Hindman168.MaskOriginalExceptionalMajorant

/-! Recover the original unconditioned prime/harmonic correlation from
the good-event conditioned source and the now-controlled whole bad event.
The probability factor is retained explicitly. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))

noncomputable def rawCorrelation
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (basePrimeMass gap t w) (fun x => expectation (maskOriginalBaseMass m gap C w)
    (originalProduct gap a C t F w x))

noncomputable def badCorrelation
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
    (fun x => ¬ maskGeneratedCopiedPrimeGood m gap t w x) (originalProduct gap a C t F w)

theorem conditionedCorrelation_eq_restricted_div
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    unshiftedCorrelation gap a ha C hC t J hJ hgap F w =
      conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
        (maskGeneratedCopiedPrimeGood m gap t w) (originalProduct gap a C t F w) /
          event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) := by
  unfold unshiftedCorrelation outsideMass
  rw [expectation_conditionalJoint, expectation_conditionMass]
  rfl

theorem rawCorrelation_split
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    rawCorrelation gap a C t F w =
      conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
        (maskGeneratedCopiedPrimeGood m gap t w) (originalProduct gap a C t F w) +
      badCorrelation gap a C t F w :=
  conditionalFiniteAverage_complement_split _ _ _ _

theorem rawCorrelation_decomposition_eventually :
    ∀ᶠ w in atTop,
    ∀ F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      rawCorrelation gap a C t F w =
        event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) *
          unshiftedCorrelation gap a ha C hC t J hJ hgap F w + badCorrelation gap a C t F w := by
  filter_upwards [(baseGoodPrimeMass_tendsto_one gap t).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
  intro F
  rw [rawCorrelation_split, conditionedCorrelation_eq_restricted_div]
  congr 1
  field_simp

include ha hC hgap htail in
theorem badCorrelation_tendsto_zero
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hF : ∀ᶠ w in atTop, ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
      |F w x base y| ≤ rowMajorant gap C t label w base y) :
    Tendsto (badCorrelation gap a C t F) atTop (𝓝 0) := by
  have hb : ∀ᶠ w in atTop, |badCorrelation gap a C t F w| ≤ originalBadMajorantMass gap a C t label w := by
    filter_upwards [original_bad_contribution_bound gap a C hC t label, hF] with w hw hf
    exact hw (F w) hf
  have hz := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb
    (originalBadMajorantMass_tendsto_zero gap a ha C hC t label hgap htail)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hz

include ha hC hgap htail in
theorem rawCorrelation_tendsto_zero_of_conditioned
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (hF : ∀ᶠ w in atTop, ∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
      |F w x base y| ≤ rowMajorant gap C t label w base y)
    (hcond : Tendsto (unshiftedCorrelation gap a ha C hC t J hJ hgap F) atTop (𝓝 0)) :
    Tendsto (rawCorrelation gap a C t F) atTop (𝓝 0) := by
  have ht := ((baseGoodPrimeMass_tendsto_one gap t).mul hcond).add
    (badCorrelation_tendsto_zero gap a ha C hC t hgap htail label F hF)
  have he : (fun w => event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) *
      unshiftedCorrelation gap a ha C hC t J hJ hgap F w + badCorrelation gap a C t F w) =ᶠ[atTop]
      rawCorrelation gap a C t F :=
    (rawCorrelation_decomposition_eventually gap a ha C hC t J hJ hgap).mono
      (fun w hw => (hw F).symm)
  have hz : Tendsto (fun w => event (basePrimeMass gap t w) (maskGeneratedCopiedPrimeGood m gap t w) *
      unshiftedCorrelation gap a ha C hC t J hJ hgap F w + badCorrelation gap a C t F w)
      atTop (𝓝 0) := by simpa only [mul_zero, add_zero] using ht
  exact hz.congr' he

end Hindman168.MaskOriginalSampling
