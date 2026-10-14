import Hindman168.AlignmentAllPivotPlanning

/-! Global scale catalogues enumerate the complete finite alternatives at
every pivot, independently of all groups, actions and palette maps. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentScheduleStep {n : ℕ} (planned : AlignmentPlannedPivot n)
    (incoming : Finset (Fin n → ℚ)) : Finset (Fin n → ℚ) :=
  alignmentScaleSetProduct incoming (alignmentPlannedMultipliers planned)

noncomputable def alignmentScheduleStates {n : ℕ} :
    List (AlignmentPlannedPivot n) → Finset (Fin n → ℚ) → Finset (Fin n → ℚ)
  | [], incoming => incoming
  | planned :: later, incoming =>
    alignmentAllScaleStates planned.pivot (alignmentForwardOptions planned.plan) incoming ∪
      alignmentScheduleStates later (alignmentScheduleStep planned incoming)

noncomputable def alignmentScheduleFinalScales {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    Finset (Fin n → ℚ) :=
  alignmentScaleSetProduct incoming (alignmentPlannedFutureProducts schedule)

theorem alignmentScheduleStep_contains {n : ℕ} (planned : AlignmentPlannedPivot n)
    (incoming : Finset (Fin n → ℚ)) (b c : Fin n → ℚ) (hb : b ∈ incoming)
    (hc : c ∈ alignmentScaleFrontier planned.pivot (alignmentForwardOptions planned.plan) {b}) :
    c ∈ alignmentScheduleStep planned incoming := by
  rw [alignmentScaleFrontier_singleton_factor] at hc
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
  exact alignmentScaleSetProduct_contains incoming _ b d hb hd

theorem alignmentScheduleStep_positive {n : ℕ} (planned : AlignmentPlannedPivot n)
    (incoming : Finset (Fin n → ℚ)) (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hchoices : ∀ stage ∈ planned.plan, ∀ p ∈ stage.choices, 0 < p.1) :
    ∀ b ∈ alignmentScheduleStep planned incoming, ∀ j, 0 < b j :=
  alignmentScaleSetProduct_positive incoming _ hin
    (alignmentPlannedMultipliers_positive planned hchoices)

theorem alignmentAllScaleStates_mono {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (first second : Finset (Fin n → ℚ))
    (h : first ⊆ second) :
    alignmentAllScaleStates i stages first ⊆ alignmentAllScaleStates i stages second := by
  induction stages generalizing first second with
  | nil => exact h
  | cons stage stages ih =>
    exact Finset.union_subset_union h
      (ih _ _ (alignmentScaleStep_mono i stage first second h))

theorem alignmentScheduleStates_contains_incoming {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    incoming ⊆ alignmentScheduleStates schedule incoming := by
  cases schedule with
  | nil => exact Finset.Subset.refl incoming
  | cons planned later =>
    exact Finset.Subset.trans (alignmentAllScaleStates_contains_incoming _ _ incoming)
      Finset.subset_union_left

theorem alignmentScheduleStates_head {n : ℕ} (planned : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    alignmentAllScaleStates planned.pivot (alignmentForwardOptions planned.plan) incoming ⊆
      alignmentScheduleStates (planned :: later) incoming := Finset.subset_union_left

theorem alignmentScheduleStates_tail {n : ℕ} (planned : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    alignmentScheduleStates later (alignmentScheduleStep planned incoming) ⊆
      alignmentScheduleStates (planned :: later) incoming := Finset.subset_union_right

theorem alignmentScheduleStates_positive {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
      ∀ p ∈ stage.choices, 0 < p.1) :
    ∀ b ∈ alignmentScheduleStates schedule incoming, ∀ j, 0 < b j := by
  induction schedule generalizing incoming with
  | nil => exact hin
  | cons planned later ih =>
    have hp := hchoices planned List.mem_cons_self
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · apply alignmentAllScaleStates_positive _ _ incoming hin _ b hb
      intro option ho
      obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp ho
      exact hp stage (List.mem_reverse.mp hs)
    · exact ih _ (alignmentScheduleStep_positive planned incoming hin hp)
        (fun p h => hchoices p (List.mem_cons_of_mem planned h)) b hb

theorem alignmentScheduleFinalScales_contains {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (b d : Fin n → ℚ) (hb : b ∈ incoming) (hd : d ∈ alignmentPlannedFutureProducts schedule) :
    alignmentMultiplyScales b d ∈ alignmentScheduleFinalScales schedule incoming :=
  alignmentScaleSetProduct_contains incoming _ b d hb hd

theorem alignmentScheduleFinalScales_positive {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
      ∀ p ∈ stage.choices, 0 < p.1) :
    ∀ b ∈ alignmentScheduleFinalScales schedule incoming, ∀ j, 0 < b j :=
  alignmentScaleSetProduct_positive incoming _ hin
    (alignmentPlannedFutureProducts_positive schedule hchoices)

end Hindman168
