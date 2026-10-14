import Hindman168.AlignmentRawBoundaryLimit
import Hindman168.AlignmentMicrocellArrayStability
import Hindman168.PrimeGoodSamples

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

def alignmentRawArrayStable {n : ℕ} (F : MasterParameterFamily) (w : ℕ) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) (S : Finset (Finset (Fin n)))
    (x : Fin n → ℕ) : Prop :=
  ∀ v ∈ V, ∀ u ∈ U, ∀ ρ : AlignmentAddingPair n i → ℕ,
    (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) → ∀ Δ : AlignmentAddingPair n i → ℤ,
    (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e x : ℤ) -
      (alignmentNaturalBlockProduct x e.targetTail : ℤ) * ρ e) →
    ∀ T ∈ S, ∀ p : ℤ,
    |p - x i| ≤ (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) →
    alignmentIntegerArrayArgument x (F.modulus w) ρ Δ T p v u / (F.gap w i.val : ℤ) =
      ((alignmentNaturalBlockProduct x T : ℤ) * x i) / (F.gap w i.val : ℤ)

theorem alignmentGlobalRawMass_geometry
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) :
    ∀ᶠ w in atTop, (∀ x, 0 ≤ globalRawMass (F.cutoff w) (primorial w) n x) ∧
      total (globalRawMass (F.cutoff w) (primorial w) n) = 1 ∧
      ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support, ∀ j : Fin n,
        x j ≤ F.cutoff w j.val ^ 2 := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have hz (j : Fin n) := (hw j.val (Finset.mem_range.mpr j.isLt)).2.2
  refine ⟨piMass_nonneg _ (fun j p => ?_), piMass_total_one _ (fun j => rawMass_total (hz j)), ?_⟩
  · rw [rawMass_apply]
    exact harmonicWeight_nonneg (hz j) p
  · intro x hx j
    have hne := Finsupp.mem_support_iff.mp hx
    rw [globalRawMass, piMass_apply] at hne
    have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j))
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window _ _ hs)).1).2.le

theorem alignment_raw_array_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ))
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ j ∈ T, j < i) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentRawArrayStable F w i q₀ V U S x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (alignment_raw_finite_boundary_tendsto hF i S hS)
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF,
      alignment_microcell_array_uniform_interval_stable hF i q₀ V U] with w hw hs
    rw [event_eq_sum _ _ (Finset.Subset.refl _), event_eq_sum _ _ (Finset.Subset.refl _)]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hbad : ¬ alignmentRawArrayStable F w i q₀ V U S x
    · have hb : ∃ T ∈ S, ¬ intervalInteriorRoot (F.gap w i.val)
          (3 * F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
          ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ) := by
        by_contra hnone
        apply hbad
        intro v hv u hu ρ hρ Δ hΔ T hT p hp
        have hinterior := not_not.mp (fun hn => hnone ⟨T, hT, hn⟩)
        rw [Nat.cast_mul] at hinterior
        exact hs v hv u hu x (fun j _ => hw.2.2 x hx j) ρ hρ Δ hΔ T (hS T hT) p (x i) hp hinterior
      rw [if_pos hbad, if_pos hb]
    · rw [if_neg hbad]
      split_ifs
      · exact hw.1 x
      · exact le_rfl

theorem alignment_raw_array_success_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ))
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ j ∈ T, j < i) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (alignmentRawArrayStable F w i q₀ V U S)) atTop (𝓝 1) := by
  have hh := (alignment_raw_array_failure_tendsto hF i q₀ V U S hS).const_sub 1
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
  rw [event_complement, hw.2.1]
  ring

end Hindman168
