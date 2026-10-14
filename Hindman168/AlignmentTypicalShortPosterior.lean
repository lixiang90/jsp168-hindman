import Hindman168.AlignmentShortPosteriorScales
import Hindman168.AlignmentShortCutoffProbability

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical

def alignmentTypicalShortPosterior {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ) : Prop :=
  (∀ j ∈ T, binaryDyadicCutoffGood (F.cutoff w j.val) (x j)) ∧
    alignmentShortCutoffGood F w i T x

theorem alignment_typicalShortPosterior_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentTypicalShortPosterior F w i T x)) atTop (𝓝 0) := by
  have hh := (master_global_binaryDyadic_discard_tendsto hF T).add
    (alignment_short_cutoff_failure_tendsto hF i T)
  simp only [add_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    simpa only [alignmentTypicalShortPosterior, not_and_or, not_forall, exists_prop] using
      event_or_le_add (globalRawMass (F.cutoff w) (primorial w) n)
        (fun x => ∃ j ∈ T, ¬ binaryDyadicCutoffGood (F.cutoff w j.val) (x j))
        (fun x => ¬ alignmentShortCutoffGood F w i T x) hw.1

theorem alignment_typicalShortPosterior_success_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (alignmentTypicalShortPosterior F w i T)) atTop (𝓝 1) := by
  have hh := (alignment_typicalShortPosterior_failure_tendsto hF i T).const_sub 1
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
  rw [event_complement, hw.2.1]
  ring

theorem alignment_typicalShortPosterior_bound_eventually
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentTypicalShortPosterior F w i T x → ∀ B : (T → ℕ) → Prop,
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) n)
        (fun y => alignmentShortExposureKey F w i T y = alignmentShortExposureKey F w i T x))
        (fun y => B (fun j : T => y j.val)) ≤
      (3 * 2 ^ T.card) * event (piMass (fun j : T => uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ) * (primorial w) ^ w) (x j.val)))) B := by
  filter_upwards [alignment_shortPosterior_scales_eventually hF i T,
    hF.raw_cutoffs_valid, hF.primorial_dvd_modulus] with w hs hz hWM
  intro x hx hg B
  have hb := alignmentShortCutoffGood_volume_le F w i T x (hF.cutoff_positive w i.val) hs.2.1 hg.2
  exact alignment_shortExposure_tail_posterior hF w i T hT x hx
    (fun j => (hz j.val (Finset.mem_range.mpr j.isLt)).2.2) hWM hg.1 hs.1
    hb.1 hb.2 hg.2.1 hg.2.2 hs.2.2 B

end Hindman168
