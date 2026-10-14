import Hindman168.AlignmentCanonicalTargets

/-! Positivity propagates through the genuine backward predecessor
construction, so every palette index queried by the plan is positive. -/

namespace Hindman168
open scoped Classical

theorem alignmentBackwardPlanFits_leading_positive {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) (requests : List (AlignmentPivotRequest n i))
    (hfit : alignmentBackwardPlanFits plan requests)
    (hchoices : ∀ stage ∈ plan, ∀ p ∈ stage.choices, 0 < p.1)
    (hrequests : ∀ request ∈ requests, ∀ a ∈ request.leading, 0 < a) :
    ∀ stage ∈ plan, ∀ a ∈ stage.target.leading, 0 < a := by
  induction plan generalizing requests with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons stage earlier ih =>
    obtain ⟨prior, rfl, hprior⟩ := hfit
    have hpred : ∀ request ∈ prior.map (alignmentPivotPredecessor stage),
        ∀ a ∈ request.leading, 0 < a := by
      intro request hrMap
      obtain ⟨r, hrPrior, rfl⟩ := List.mem_map.mp hrMap
      exact alignment_pivot_predecessor_positive stage r (hchoices stage List.mem_cons_self)
        (hrequests r (List.mem_append_left _ hrPrior))
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hrequests a.target (List.mem_append_right _ (List.mem_singleton_self _))
    · exact ih _ hprior (fun p hp => hchoices p (List.mem_cons_of_mem stage hp)) hpred a ha

theorem alignmentAllPivotFits_leading_positive {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (schedule : List (AlignmentPlannedPivot n))
    (hfit : alignmentAllPivotFits requests schedule)
    (hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan, ∀ p ∈ stage.choices, 0 < p.1)
    (hrequests : ∀ i, ∀ request ∈ requests i, ∀ a ∈ request.leading, 0 < a) :
    ∀ planned ∈ schedule, ∀ stage ∈ planned.plan, ∀ a ∈ stage.target.leading, 0 < a := by
  induction schedule with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons planned later ih =>
    obtain ⟨hhead, htail⟩ := hfit
    have hclater : ∀ p ∈ later, ∀ stage ∈ p.plan, ∀ c ∈ stage.choices, 0 < c.1 :=
      fun p hp => hchoices p (List.mem_cons_of_mem planned hp)
    have hfutures := alignmentPlannedFutureProducts_positive later hclater
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · apply alignmentBackwardPlanFits_leading_positive p.plan _ hhead
        (hchoices p List.mem_cons_self)
      intro request hrMap
      obtain ⟨r, hrOriginal, rfl⟩ := List.mem_map.mp hrMap
      exact alignmentFutureRequest_leading_positive _ r hfutures (hrequests p.pivot r hrOriginal)
    · exact ih htail hclater p hp

theorem alignmentCanonicalRequests_leading_positive (n : ℕ) (i : Fin n) :
    ∀ request ∈ alignmentCanonicalRequests n i, ∀ a ∈ request.leading, 0 < a := by
  intro request hr a ha
  obtain ⟨T, _, rfl⟩ := List.mem_map.mp hr
  have h : a = 1 := Finset.mem_singleton.mp ha
  rw [h]
  exact zero_lt_one

end Hindman168
