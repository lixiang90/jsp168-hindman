import Hindman168.MaskOriginalRootTranslation

/-! Root smoothing under the unchanged original normalized joint law.
The explicit lattice translation error is rapidly small at the actual gap
budget and controls every polynomially bounded test on original good tuples. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

local notation "S" => maskOriginalSampling m gap a ha C hC t J hJ hgap
local notation "χ" => outsideMass gap a ha C hC t J hJ hgap

noncomputable def rootErrorCap (w : ℕ) : ℝ :=
  ∑ col : Fin (m + 1), translationError
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)
    (rootShiftCap (m := m) gap w)

include hC hgap in
theorem rootErrorCap_rapid :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (rootErrorCap gap C) := by
  apply RapidlySmall.finset_sum Finset.univ
  intro col _
  exact translationError_rapid (rootShift_sampling_growth gap C hC hgap col)
    (Eventually.of_forall (fun w => (by decide : 1 ≤ 2).trans
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))

include hC in
theorem rootErrorCap_eventually_nonneg :
    ∀ᶠ w in atTop, 0 ≤ rootErrorCap gap C w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  unfold rootErrorCap
  apply Finset.sum_nonneg
  intro col _
  have hv := hw ((C w).pivot col) (hC w col (by simp [Chain.block]))
  unfold translationError
  exact div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hv.2.1).le)

include ha hC in
theorem rootShift_distance_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ u₀,
      u₀ ∈ (rootMass (m := m) gap w).support →
      (∑ col : Fin (m + 1), distance
        ((integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)).mapDomain
          (fun y => y + rootShift gap a C t w x u₀ col))
        (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))) ≤
          rootErrorCap gap C w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [rootShift_W_eventually gap a ha C hC t,
    rootShift_size_eventually gap a ha C hC t, hF.raw_cutoffs_valid] with w hW hsize hv
  intro x hx u₀ hu
  unfold rootErrorCap
  apply Finset.sum_le_sum
  intro col _
  have hc := hv ((C w).pivot col) (hC w col (by simp [Chain.block]))
  have hh : |(rootShift gap a C t w x u₀ col : ℝ)| ≤ rootShiftCap (m := m) gap w := by
    have hn : ((rootShift gap a C t w x u₀ col).natAbs : ℝ) ≤ rootShiftCap (m := m) gap w := by
      exact_mod_cast hsize x hx u₀ hu col
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hn
  have he := integer_harmonic_translation_error hc.1 (primorial_pos w) hc.2.1 (hW x hx u₀ col)
  have hden : 0 ≤ (((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ) *
      (Real.log ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ) -
        (primorial w : ℝ) / (maskGeneratedMaster m gap).cutoff w ((C w).pivot col))) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hc.2.1).le
  unfold translationError
  exact (he.trans (min_le_right _ _)).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hden)

noncomputable def rootSmoothedAverage
    (T : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → (Fin (m + 1) → ℤ) → ℝ)
    (w : ℕ) : ℝ :=
  expectation (χ w) (fun p => expectation (rootMass (m := m) gap w)
    (fun u₀ => T w p.1 (fun col => p.2 col + rootShift gap a C t w p.1 u₀ col)))

noncomputable def originalTestAverage
    (T : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → (Fin (m + 1) → ℤ) → ℝ)
    (w : ℕ) : ℝ := expectation (χ w) (fun p => T w p.1 p.2)

theorem rootSmoothedAverage_eq_shift
    (T : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → (Fin (m + 1) → ℤ) → ℝ)
    (w : ℕ) :
    rootSmoothedAverage gap a ha C hC t J hJ hgap T w =
      expectation (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w))
        (fun x => expectation (rootMass (m := m) gap w) (fun u₀ =>
          expectation (maskOriginalBaseMass m gap C w) (fun z =>
            T w x (fun col => z col + rootShift gap a C t w x u₀ col)))) := by
  unfold rootSmoothedAverage outsideMass
  rw [expectation_conditionalJoint]
  apply congrArg (expectation (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)))
  funext x
  exact expectation_comm _ _ _

theorem root_smoothing_difference_eventually_bound
    (T : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → (Fin (m + 1) → ℤ) → ℝ)
    (q : ℕ)
    (hT : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z,
      |T w x z| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q) :
    ∀ᶠ w in atTop,
      |rootSmoothedAverage gap a ha C hC t J hJ hgap T w -
        originalTestAverage gap a ha C hC t J hJ hgap T w| ≤
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q * rootErrorCap gap C w := by
  filter_upwards [(S).conditioned_prime_probability_eventually,
    base_coordinates_probability_eventually gap C hC,
    rootShift_distance_eventually gap a ha C hC t, hT] with w hp hc hδ ht
  rw [rootSmoothedAverage_eq_shift gap a ha C hC t J hJ hgap T w]
  unfold originalTestAverage outsideMass
  rw [expectation_conditionalJoint]
  have he := expectation_difference_support_bound
    (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) hp.1
    (fun x => expectation (rootMass (m := m) gap w) (fun u₀ =>
      expectation (maskOriginalBaseMass m gap C w) (fun z =>
        T w x (fun col => z col + rootShift gap a C t w x u₀ col))))
    (fun x => expectation (maskOriginalBaseMass m gap C w) (T w x))
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q * rootErrorCap gap C w) (by
      intro x hx
      have hxG := conditionMass_mem_support_event _ (maskGeneratedCopiedPrimeGood m gap t w) x hx
      exact averaged_piMass_translation_expectation_bound
        (fun col : Fin (m + 1) => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (rootMass (m := m) gap w) (rootShift gap a C t w x) (T w x)
        (fun col => (hc col).1) (fun col => (hc col).2)
        (rootMass_probability gap w).1 (rootMass_probability gap w).2
        (by positivity) (ht x hxG) (fun u₀ hu => hδ x hxG u₀ hu))
  have htot : total (conditionMass ((S).primeMass w) (maskGeneratedCopiedPrimeGood m gap t w)) = 1 := hp.2
  have hs := congrArg (fun r : ℝ => r *
    (((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q * rootErrorCap gap C w)) htot
  exact he.trans (le_of_eq (hs.trans (one_mul _)))

theorem root_smoothing_difference_rapid
    (T : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → (Fin (m + 1) → ℤ) → ℝ)
    (q : ℕ)
    (hT : ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z,
      |T w x z| ≤ ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ) ^ q) :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (fun w => rootSmoothedAverage gap a ha C hC t J hJ hgap T w -
        originalTestAverage gap a ha C hC t J hJ hgap T w) := by
  apply ((rootErrorCap_rapid gap C hC hgap).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2)
        ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val))) q).of_abs_le
  filter_upwards [root_smoothing_difference_eventually_bound gap a ha C hC t J hJ hgap T q hT]
    with w hw
  exact hw.trans (le_abs_self _)

end Hindman168.MaskOriginalSampling
