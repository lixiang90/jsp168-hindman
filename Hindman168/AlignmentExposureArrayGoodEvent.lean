import Hindman168.AlignmentExposureStabilityProbability

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

def alignmentExposureArrayStable {n : ℕ} (F : MasterParameterFamily) (w : ℕ)
    (i : Fin n) (q₀ C : ℕ) (T : Finset (Fin n))
    (V U : Finset (AlignmentAddingPair n i → ℤ)) (x : Fin n → ℕ) : Prop :=
  ∀ y : Fin n → ℕ, (∀ j, j < i → y j ≤ F.cutoff w j.val ^ 2) →
    alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y →
    ∀ v ∈ V, ∀ u ∈ U, ∀ ρ : AlignmentAddingPair n i → ℕ,
    (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) → ∀ Δ : AlignmentAddingPair n i → ℤ,
    (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e y : ℤ) -
      (alignmentNaturalBlockProduct y e.targetTail : ℤ) * ρ e) →
    ∀ p : ℤ, |p - y i| ≤ (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) →
    alignmentIntegerArrayArgument y (F.modulus w) ρ Δ T p v u / (F.gap w i.val : ℤ) =
      ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ)

theorem alignmentGlobalRawMass_support_positive
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support) (j : Fin n) :
    0 < x j := by
  have hne := Finsupp.mem_support_iff.mp hx
  rw [globalRawMass, piMass_apply] at hne
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j))
  exact (hF.cutoff_positive w j.val).trans_le
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window _ _ hs)).1).1

theorem alignment_exposure_array_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentExposureArrayStable F w i q₀ C T V U x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (alignment_raw_block_boundary_multiple_tendsto hF i (C + 3) T hT)
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF,
      alignment_exposure_uniform_interval_stable hF i q₀ C V U] with w hw hi
    rw [event_eq_sum _ _ (Finset.Subset.refl _), event_eq_sum _ _ (Finset.Subset.refl _)]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hbad : ¬ alignmentExposureArrayStable F w i q₀ C T V U x
    · have hb : ¬ intervalInteriorRoot (F.gap w i.val)
          ((C + 3) * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
          ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) := by
        intro hinterior
        apply hbad
        intro y hy hkey
        exact hi T hT x y (fun j _ => hw.2.2 x hx j)
          (fun j _ => alignmentGlobalRawMass_support_positive hF w x hx j) hy hkey hinterior
      rw [if_pos hbad, if_pos hb]
    · rw [if_neg hbad]
      split_ifs
      · exact le_rfl
      · exact hw.1 x

theorem alignment_exposure_array_success_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (alignmentExposureArrayStable F w i q₀ C T V U)) atTop (𝓝 1) := by
  have hh := (alignment_exposure_array_failure_tendsto hF i q₀ C T hT V U).const_sub 1
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
  rw [event_complement, hw.2.1]
  ring

end Hindman168
