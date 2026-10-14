import Hindman168.SelectedAlignmentShortPosteriorScales

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical

theorem selected_alignment_short_cutoff_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i)
    (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentShortCutoffGood (alignmentGeometryWithGap F i.val gap.val) w i T x))
      atTop (𝓝 0) := by
  have hc : (1 : ℝ) ≤ 2 ^ T.card := one_le_pow₀ (by norm_num)
  have hp := master_failedCutoffShortBin_tendsto hF (fun _ => i)
    (fun w => (alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w) : ℝ))
    (fun _ => 1) hc (Eventually.of_forall (fun w => by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have hgi : F.gap w gap.val ≤ F.gap w i.val := by
        rcases lt_or_eq_of_le hgap with hlt | heq
        · exact Nat.le_of_dvd (hF.gap_positive w _) (hF.gap_earlier_dvd w _ _ hlt)
        · subst gap; exact le_rfl
      exact_mod_cast (alignedSqrtWidth_le (F.gap w gap.val) (F.modulus w)).trans hgi))
    (Eventually.of_forall (fun _ => by norm_num))
  have hglobal : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => failedCutoffShortBin (F.cutoff w i.val)
        (alignedSqrtMicrocellWidth (F.gap w gap.val) (F.modulus w)) 1 (2 ^ T.card) (x i)))
      atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [hF.raw_cutoffs_valid] with w hw
    symm
    exact event_piMass_coordinate _
      (fun j : Fin n => rawMass_total (hw j.val (Finset.mem_range.mpr j.isLt)).2.2) i _
  apply squeeze_zero' _ _ hglobal
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF,
      master_microcell_eventually_positive hF (fun _ => gap)] with w hw hR
    apply event_mono_on_support _ _ _ hw.1
    intro x hx hbad
    have hh := alignment_short_cutoff_failure_normalized (alignmentGeometryWithGap F i.val gap.val) w i T x
      (fun j _ => alignmentGlobalRawMass_support_positive hF w x hx j)
      (by simpa only [alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hR) hbad
    simpa only [alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus,
      alignmentGeometryWithGap_cutoff] using hh

theorem selected_alignment_typicalShortPosterior_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i)
    (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentTypicalShortPosterior (alignmentGeometryWithGap F i.val gap.val) w i T x))
      atTop (𝓝 0) := by
  have hh := (master_global_binaryDyadic_discard_tendsto hF T).add
    (selected_alignment_short_cutoff_failure_tendsto hF i gap hgap T)
  simp only [add_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    simpa only [alignmentTypicalShortPosterior, alignmentGeometryWithGap_cutoff,
      not_and_or, not_forall, exists_prop] using
      event_or_le_add (globalRawMass (F.cutoff w) (primorial w) n)
        (fun x => ∃ j ∈ T, ¬ binaryDyadicCutoffGood (F.cutoff w j.val) (x j))
        (fun x => ¬ alignmentShortCutoffGood (alignmentGeometryWithGap F i.val gap.val) w i T x) hw.1

theorem selected_alignment_typicalShortPosterior_bound_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentTypicalShortPosterior (alignmentGeometryWithGap F i.val gap.val) w i T x →
      ∀ B : (T → ℕ) → Prop,
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
        (fun y => alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap.val) w i T y =
          alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap.val) w i T x))
        (fun y => B (fun j : T => y j.val)) ≤
      (3 * 2 ^ T.card) * event (piMass (fun j : T => uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)))) B := by
  filter_upwards [selected_alignment_shortPosterior_scales_eventually hF i gap hgap T,
    hF.raw_cutoffs_valid, hF.primorial_dvd_modulus] with w hs hz hWM
  intro x hx hg B
  have hb := alignmentShortCutoffGood_volume_le (alignmentGeometryWithGap F i.val gap.val) w i T x
    (hF.cutoff_positive w i.val)
    (by simpa only [alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus,
      alignmentGeometryWithGap_cutoff] using hs.2.1) hg.2
  exact selected_alignment_shortExposure_tail_posterior hF gap.val w i T hT x hx
    (fun j => (hz j.val (Finset.mem_range.mpr j.isLt)).2.2) hWM hg.1 hs.1
    hb.1 hb.2 hg.2.1 hg.2.2 hs.2.2 B
theorem selected_alignment_typicalShortPosterior_success_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i gap : Fin n) (hgap : gap ≤ i)
    (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (alignmentTypicalShortPosterior (alignmentGeometryWithGap F i.val gap.val) w i T))
      atTop (𝓝 1) := by
  have hh := (selected_alignment_typicalShortPosterior_failure_tendsto hF i gap hgap T).const_sub 1
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
  rw [event_complement, hw.2.1]
  ring

end Hindman168
