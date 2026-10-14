import Hindman168.AlignmentFuturePivotPlan

/-! The plans at later pivots are chosen first. Their actual finite
multiplier catalogues determine the earlier pivot's terminal budgets. -/

namespace Hindman168
universe u v
open scoped Classical

structure AlignmentPlannedPivot (n : ℕ) where
  pivot : Fin n
  plan : List (AlignmentPivotStage n pivot)

noncomputable def alignmentPlannedMultipliers {n : ℕ} (planned : AlignmentPlannedPivot n) :
    Finset (Fin n → ℚ) :=
  alignmentScaleFrontier planned.pivot (alignmentForwardOptions planned.plan) {fun _ => 1}

noncomputable def alignmentPlannedFutureProducts {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) : Finset (Fin n → ℚ) :=
  alignmentFutureProducts (schedule.map alignmentPlannedMultipliers)

noncomputable def alignmentAllPivotFits {n : ℕ}
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i)) :
    List (AlignmentPlannedPivot n) → Prop
  | [] => True
  | planned :: later =>
    alignmentBackwardPlanFits planned.plan
      ((requests planned.pivot).map (alignmentFutureRequest (alignmentPlannedFutureProducts later))) ∧
      alignmentAllPivotFits requests later

theorem alignmentPlannedMultipliers_positive {n : ℕ} (planned : AlignmentPlannedPivot n)
    (hchoices : ∀ stage ∈ planned.plan, ∀ p ∈ stage.choices, 0 < p.1) :
    ∀ d ∈ alignmentPlannedMultipliers planned, ∀ j, 0 < d j := by
  apply alignmentScaleFrontier_positive
  · intro d hd
    have h : d = fun _ => 1 := Finset.mem_singleton.mp hd
    subst d
    intro j
    exact zero_lt_one
  · intro option ho
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp ho
    exact hchoices stage (List.mem_reverse.mp hs)

theorem alignmentPlannedFutureProducts_positive {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n))
    (hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
      ∀ p ∈ stage.choices, 0 < p.1) :
    ∀ d ∈ alignmentPlannedFutureProducts schedule, ∀ j, 0 < d j := by
  apply alignmentFutureProducts_positive
  intro A hA
  obtain ⟨planned, hp, rfl⟩ := List.mem_map.mp hA
  exact alignmentPlannedMultipliers_positive planned (hchoices planned hp)

theorem alignment_all_pivot_plans_exist {n : ℕ} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (requests : ∀ i : Fin n, List (AlignmentPivotRequest n i)) (pivots : List (Fin n)) :
    ∃ schedule : List (AlignmentPlannedPivot n),
      schedule.map AlignmentPlannedPivot.pivot = pivots ∧ alignmentAllPivotFits requests schedule ∧
      ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
        AlignmentPivotStageWorks.{u, v} s Color stage := by
  induction pivots with
  | nil => exact ⟨[], rfl, trivial, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
  | cons i pivots ih =>
    obtain ⟨later, hpivots, hfitlater, hworks⟩ := ih
    obtain ⟨plan, hfit, hplan⟩ := alignment_backward_plan_exists.{u, v} (Color := Color)
      s hrec ((requests i).map (alignmentFutureRequest (alignmentPlannedFutureProducts later)))
    let planned : AlignmentPlannedPivot n := ⟨i, plan⟩
    refine ⟨planned :: later, ?_, ⟨hfit, hfitlater⟩, ?_⟩
    · change i :: later.map AlignmentPlannedPivot.pivot = i :: pivots
      exact congrArg (List.cons i) hpivots
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hplan
      · exact hworks p hp

end Hindman168
