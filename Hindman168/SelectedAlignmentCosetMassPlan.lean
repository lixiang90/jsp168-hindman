import Hindman168.AlignmentJointRouteReadingsCover

/-! The SAME finite recurrence plan supplies fit, positive scales, execution,
and the eventual coset cover. All choices precede the joint model and theta. -/
namespace Hindman168
open scoped Classical

noncomputable def selectedAlignmentCosetPlan {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) : List (AlignmentPivotStage n i) :=
  Classical.choose (alignment_backward_plan_exists.{0,0} (Color := κ → Bool)
    (s+1) (hasAlignmentMonomialRecurrence (s+1)) requests)

theorem selected_alignment_coset_plan_fits {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) :
    alignmentBackwardPlanFits (selectedAlignmentCosetPlan (κ := κ) s requests) requests :=
  (Classical.choose_spec (alignment_backward_plan_exists.{0,0} (Color := κ → Bool)
    (s+1) (hasAlignmentMonomialRecurrence (s+1)) requests)).1

theorem selected_alignment_coset_plan_works {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) :
    ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      AlignmentPivotStageWorks.{0,0} (s+1) (κ → Bool) stage :=
  (Classical.choose_spec (alignment_backward_plan_exists.{0,0} (Color := κ → Bool)
    (s+1) (hasAlignmentMonomialRecurrence (s+1)) requests)).2

theorem selected_alignment_coset_plan_positive {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) :
    ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests, ∀ p ∈ stage.choices, 0 < p.1 :=
  fun stage hs => (selected_alignment_coset_plan_works (κ := κ) s requests stage hs).1

noncomputable def selectedAlignmentCosetClearing {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) (incoming : Finset (Fin n → ℚ)) : ℕ :=
  Classical.choose (alignment_pivot_plan_denominators
    (selectedAlignmentCosetPlan (κ := κ) s requests) incoming)

theorem selected_alignment_coset_clearing_pos {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) (incoming : Finset (Fin n → ℚ)) :
    0 < selectedAlignmentCosetClearing (κ := κ) s requests incoming :=
  (Classical.choose_spec (alignment_pivot_plan_denominators
    (selectedAlignmentCosetPlan (κ := κ) s requests) incoming)).1

theorem selected_alignment_coset_clearing_denominators {n : ℕ} {i : Fin n} {κ : Type} [Finite κ]
    (s : ℕ) (requests : List (AlignmentPivotRequest n i)) (incoming : Finset (Fin n → ℚ)) :
    ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions
        (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (selectedAlignmentCosetClearing (κ := κ) s requests incoming : ℚ) *
            alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range :=
  (Classical.choose_spec (alignment_pivot_plan_denominators
    (selectedAlignmentCosetPlan (κ := κ) s requests) incoming)).2
end Hindman168
