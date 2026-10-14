import Hindman168.AlignmentCanonicalTargets
import Hindman168.AlignmentNilpotentRecurrence

/-! The original canonical finite-word plan, with its nilpotent recurrence
input supplied by the actual formalized PET theorem. -/
namespace Hindman168
universe u v

theorem alignment_canonical_finite_word_plan_proved {n : ℕ} {Color : Type} [Finite Color]
    (s : ℕ) :
    ∃ schedule : List (AlignmentPlannedPivot n),
      schedule.map AlignmentPlannedPivot.pivot = List.finRange n ∧
      ∃ q₀ : ℕ, 0 < q₀ ∧
      (∀ planned ∈ schedule,
        ∀ b ∈ alignmentScheduleStates schedule {fun _ => 1} ∪
          alignmentScheduleFinalScales schedule {fun _ => 1},
          ∀ l ∈ alignmentScheduleLetters (alignmentCanonicalRequests n) planned,
            (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range) ∧
      ∀ (G : Fin n → Type u) (X : Fin n → Type v)
        [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
        (L : ∀ i, AlignmentAddingPair n i → G i)
        (_hG : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥)
        (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color) (centers : ∀ i, X i),
        ∃ final ∈ alignmentScheduleFinalScales schedule {fun _ => 1},
          final ∈ alignmentScheduleStates schedule {fun _ => 1} ∧ (∀ j, 0 < final j) ∧
          alignmentScheduleRealizes G X q₀ L palette (alignmentCanonicalRequests n) centers
            schedule (fun _ => 1) final ∧
          ∀ i : Fin n, ∃ y : X i, ∀ T ∈ alignmentCanonicalTargetTails n i,
            ∀ selected : List (AlignmentAddingPair n i),
              selected.Sublist (alignmentCanonicalTargetPairs n i T) →
              palette i (insert i T) (finiteScaleBlockProduct final (insert i T)) y =
                palette i (insert i T) (finiteScaleBlockProduct final (insert i T))
                  (alignmentWordValue q₀ final (L i)
                    (selected.map (fun e => (e, (1 : ℚ)))) • y) := by
  exact alignment_canonical_finite_word_plan s (hasAlignmentMonomialRecurrence s)

end Hindman168
