import Hindman168.AlignmentSchedulePaths

/-! One denominator covers every stage generator, every admitted jump
letter, and every original terminal test throughout the whole schedule. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentScheduleLetters {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (planned : AlignmentPlannedPivot n) : Finset (AlignmentAddingPair n planned.pivot × ℚ) :=
  (alignmentPivotPlanLetters planned.plan ∪
    (requests planned.pivot).toFinset.biUnion (fun request => alignmentWordLetters request.words)) ∪
    planned.plan.toFinset.biUnion (fun stage => stage.choices.biUnion (fun p => p.2.toFinset))

noncomputable def alignmentScheduleScalars {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (B : Finset (Fin n → ℚ)) : Finset ℚ :=
  schedule.toFinset.biUnion (fun planned => B.biUnion (fun b =>
    (alignmentScheduleLetters requests planned).image (alignmentLetterScalar b)))

theorem alignmentScheduleLetters_stage {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (planned : AlignmentPlannedPivot n) (stage : AlignmentPivotStage n planned.pivot)
    (hs : stage ∈ planned.plan) (l : AlignmentAddingPair n planned.pivot × ℚ)
    (hl : l ∈ alignmentWordLetters stage.target.words) :
    l ∈ alignmentScheduleLetters requests planned :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hl⟩))

theorem alignmentScheduleLetters_request {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (planned : AlignmentPlannedPivot n) (request : AlignmentPivotRequest n planned.pivot)
    (hr : request ∈ requests planned.pivot) (l : AlignmentAddingPair n planned.pivot × ℚ)
    (hl : l ∈ alignmentWordLetters request.words) :
    l ∈ alignmentScheduleLetters requests planned :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨request, List.mem_toFinset.mpr hr, hl⟩))

theorem alignmentScheduleLetters_jump {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (planned : AlignmentPlannedPivot n) (stage : AlignmentPivotStage n planned.pivot)
    (hs : stage ∈ planned.plan) (p : ℕ × List (AlignmentAddingPair n planned.pivot × ℚ))
    (hp : p ∈ stage.choices) (l : AlignmentAddingPair n planned.pivot × ℚ) (hl : l ∈ p.2) :
    l ∈ alignmentScheduleLetters requests planned :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs,
    Finset.mem_biUnion.mpr ⟨p, hp, List.mem_toFinset.mpr hl⟩⟩)

theorem alignment_schedule_finite_denominators {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (B : Finset (Fin n → ℚ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ planned ∈ schedule, ∀ b ∈ B,
      ∀ l ∈ alignmentScheduleLetters requests planned,
        (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨q₀, hq, hint⟩ := rational_finite_family_integer_multiplier
    (alignmentScheduleScalars requests schedule B) id
  refine ⟨q₀, hq, ?_⟩
  intro planned hp b hb l hl
  exact hint _ (Finset.mem_biUnion.mpr ⟨planned, List.mem_toFinset.mpr hp,
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩⟩)

end Hindman168
