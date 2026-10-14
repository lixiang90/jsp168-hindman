import Hindman168.AlignmentPlanPositivity

/-! All recurrence palette indices and original terminal indices are in
one finite positive list, closed under every final block product. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentPlannedPaletteBudget {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (planned : AlignmentPlannedPivot n) :
    Finset (Finset (Fin n) × ℚ) :=
  planned.plan.toFinset.biUnion (fun stage => stage.target.leading.image
    (fun a => (insert planned.pivot stage.target.tail, a))) ∪
  (requests planned.pivot).toFinset.biUnion (fun request => request.leading.image
    (fun a => (insert planned.pivot request.tail, a)))

noncomputable def alignmentSchedulePaletteIndices {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (B : Finset (Fin n → ℚ)) : Finset ℚ :=
  schedule.toFinset.biUnion (fun planned => B.biUnion (fun b =>
    (alignmentPlannedPaletteBudget requests planned).image
      (fun p => p.2 * finiteScaleBlockProduct b p.1)))

noncomputable def alignmentSchedulePredictionScales {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) : Finset ℚ :=
  finiteScaleProductClosure (alignmentScheduleFinalScales schedule incoming)
    (alignmentSchedulePaletteIndices requests schedule
      (alignmentScheduleStates schedule incoming ∪ alignmentScheduleFinalScales schedule incoming))

theorem alignmentPlannedPaletteBudget_stage {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (planned : AlignmentPlannedPivot n)
    (stage : AlignmentPivotStage n planned.pivot) (hs : stage ∈ planned.plan)
    (a : ℚ) (ha : a ∈ stage.target.leading) :
    (insert planned.pivot stage.target.tail, a) ∈ alignmentPlannedPaletteBudget requests planned :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr
    ⟨stage, List.mem_toFinset.mpr hs, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)

theorem alignmentPlannedPaletteBudget_request {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (planned : AlignmentPlannedPivot n)
    (request : AlignmentPivotRequest n planned.pivot) (hr : request ∈ requests planned.pivot)
    (a : ℚ) (ha : a ∈ request.leading) :
    (insert planned.pivot request.tail, a) ∈ alignmentPlannedPaletteBudget requests planned :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨request, List.mem_toFinset.mpr hr, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)

theorem alignmentPlannedPaletteBudget_positive {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (planned : AlignmentPlannedPivot n)
    (hstage : ∀ stage ∈ planned.plan, ∀ a ∈ stage.target.leading, 0 < a)
    (hrequest : ∀ request ∈ requests planned.pivot, ∀ a ∈ request.leading, 0 < a) :
    ∀ p ∈ alignmentPlannedPaletteBudget requests planned, 0 < p.2 := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨stage, hs, himage⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp himage
    exact hstage stage (List.mem_toFinset.mp hs) a ha
  · obtain ⟨request, hr, himage⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp himage
    exact hrequest request (List.mem_toFinset.mp hr) a ha

theorem alignmentSchedulePaletteIndices_contains {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (B : Finset (Fin n → ℚ))
    (planned : AlignmentPlannedPivot n) (hp : planned ∈ schedule) (b : Fin n → ℚ) (hb : b ∈ B)
    (p : Finset (Fin n) × ℚ) (hbudget : p ∈ alignmentPlannedPaletteBudget requests planned) :
    p.2 * finiteScaleBlockProduct b p.1 ∈ alignmentSchedulePaletteIndices requests schedule B :=
  Finset.mem_biUnion.mpr ⟨planned, List.mem_toFinset.mpr hp,
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨p, hbudget, rfl⟩⟩⟩

theorem alignmentSchedulePaletteIndices_positive {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (B : Finset (Fin n → ℚ))
    (hB : ∀ b ∈ B, ∀ j, 0 < b j)
    (hbudget : ∀ planned ∈ schedule, ∀ p ∈ alignmentPlannedPaletteBudget requests planned, 0 < p.2) :
    ∀ a ∈ alignmentSchedulePaletteIndices requests schedule B, 0 < a := by
  intro a ha
  obtain ⟨planned, hp, hBmem⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨b, hb, himage⟩ := Finset.mem_biUnion.mp hBmem
  obtain ⟨p, hpb, rfl⟩ := Finset.mem_image.mp himage
  exact mul_pos (hbudget planned (List.mem_toFinset.mp hp) p hpb)
    (finiteScaleBlockProduct_positive b (hB b hb) p.1)

theorem alignmentSchedulePredictionScales_contains {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    alignmentSchedulePaletteIndices requests schedule
      (alignmentScheduleStates schedule incoming ∪ alignmentScheduleFinalScales schedule incoming) ⊆
        alignmentSchedulePredictionScales requests schedule incoming :=
  finiteScaleProductClosure_contains _ _

theorem alignmentSchedulePredictionScales_closed {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    FiniteScaleClosure (alignmentScheduleFinalScales schedule incoming)
      (alignmentSchedulePredictionScales requests schedule incoming) :=
  finiteScaleProductClosure_closed _ _

theorem alignmentSchedulePredictionScales_positive {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (hfit : alignmentAllPivotFits requests schedule)
    (hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan, ∀ p ∈ stage.choices, 0 < p.1)
    (hrequests : ∀ i, ∀ request ∈ requests i, ∀ a ∈ request.leading, 0 < a)
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j) :
    ∀ a ∈ alignmentSchedulePredictionScales requests schedule incoming, 0 < a := by
  have hs := alignmentScheduleStates_positive schedule incoming hin hchoices
  have hf := alignmentScheduleFinalScales_positive schedule incoming hin hchoices
  have hstages := alignmentAllPivotFits_leading_positive requests schedule hfit hchoices hrequests
  apply finiteScaleProductClosure_positive _ _ hf
  apply alignmentSchedulePaletteIndices_positive
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hs b hb
    · exact hf b hb
  · intro planned hp
    exact alignmentPlannedPaletteBudget_positive requests planned (hstages planned hp)
      (hrequests planned.pivot)

theorem alignmentSchedulePredictionScales_stage {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (planned : AlignmentPlannedPivot n) (hp : planned ∈ schedule)
    (stage : AlignmentPivotStage n planned.pivot) (hs : stage ∈ planned.plan)
    (b : Fin n → ℚ) (hb : b ∈ alignmentScheduleStates schedule incoming)
    (a : ℚ) (ha : a ∈ stage.target.leading) :
    a * finiteScaleBlockProduct b (insert planned.pivot stage.target.tail) ∈
      alignmentSchedulePredictionScales requests schedule incoming :=
  alignmentSchedulePredictionScales_contains requests schedule incoming
    (alignmentSchedulePaletteIndices_contains requests schedule _ planned hp b
      (Finset.mem_union_left _ hb) _ (alignmentPlannedPaletteBudget_stage requests planned stage hs a ha))

end Hindman168
