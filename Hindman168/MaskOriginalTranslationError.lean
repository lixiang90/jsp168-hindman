import Hindman168.MaskOriginalTranslationBounds

/-! One explicit error cap controls every actual inserted shift on the
original quotient-interval support. Its rapid decay follows from actual
master growth and absorbs every fixed polynomial loss at the gap budget. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)

noncomputable def insertionErrorCap (w : ℕ) : ℝ :=
  ∑ col : Fin (m + 1), translationError
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)
    (insertionShiftCap (m := m) gap w)

include hC hgap in
theorem insertionErrorCap_rapid :
    RapidlySmall atTop (fun w => ((maskGeneratedMaster m gap).auxiliary w (gap w).val : ℝ))
      (insertionErrorCap gap C) := by
  apply RapidlySmall.finset_sum Finset.univ
  intro col _
  exact translationError_rapid (insertionShift_sampling_growth gap C hC hgap col)
    (Eventually.of_forall (fun w => (by decide : 1 ≤ 2).trans
      ((maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val)))

include hC in
theorem insertionErrorCap_eventually_nonneg :
    ∀ᶠ w in atTop, 0 ≤ insertionErrorCap gap C w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  unfold insertionErrorCap
  apply Finset.sum_nonneg
  intro col _
  have hv := hw ((C w).pivot col) (hC w col (by simp [Chain.block]))
  unfold translationError
  exact div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hv.2.1).le)

include hC in
theorem base_coordinates_probability_eventually :
    ∀ᶠ w in atTop, ∀ col : Fin (m + 1),
      (∀ z, 0 ≤ integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w) z) ∧
      total (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro col
  have hv := hw ((C w).pivot col) (hC w col (by simp [Chain.block]))
  exact ⟨integerMass_nonneg hv.2.2, integerMass_total hv.2.2⟩

include ha hC in
theorem insertionShift_distance_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z u,
      u ∈ (piMass (completedDirectionMass gap a ha C hC t J hJ hgap w (x, z))).support →
      (∑ col : Fin (m + 1), distance
        ((integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w)).mapDomain
          (fun y => y + insertionShift gap a C t w x u col))
        (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))) ≤
          insertionErrorCap gap C w := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [insertionShift_W_eventually gap a ha C hC t,
    insertionShift_size_eventually gap a ha C hC t, hF.raw_cutoffs_valid] with w hW hsize hv
  intro x hx z u hu
  have huR := supported_direction_natAbs_le_gap gap a ha C hC t J hJ hgap w x hx z u hu
  unfold insertionErrorCap
  apply Finset.sum_le_sum
  intro col _
  have hc := hv ((C w).pivot col) (hC w col (by simp [Chain.block]))
  have hh : |(insertionShift gap a C t w x u col : ℝ)| ≤ insertionShiftCap (m := m) gap w := by
    have hn : ((insertionShift gap a C t w x u col).natAbs : ℝ) ≤ insertionShiftCap (m := m) gap w := by
      exact_mod_cast hsize x hx u huR col
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hn
  have he := integer_harmonic_translation_error hc.1 (primorial_pos w) hc.2.1 (hW x hx u col)
  have hden : 0 ≤ (((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ) *
      (Real.log ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ) -
        (primorial w : ℝ) / (maskGeneratedMaster m gap).cutoff w ((C w).pivot col))) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_pos.mpr hc.2.1).le
  unfold translationError
  exact (he.trans (min_le_right _ _)).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hden)

end Hindman168.MaskOriginalSampling
