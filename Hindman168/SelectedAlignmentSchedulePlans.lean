import Hindman168.AlignmentGlobalPaletteScales
import Hindman168.SelectedAlignmentCosetMassRecurrence
import Hindman168.AlignmentJointRouteReadingsCatalogue

/-! A later-first schedule using the literal selected coset plan at every
pivot. Its choices depend only on the finite parameters, before any model,
threshold, raw embedding, or master parameter family. -/
namespace Hindman168
open scoped Classical

noncomputable def selectedAlignmentScheduleRequests {n : ℕ}
    (later : List (AlignmentPlannedPivot n)) (i : Fin n) : List (AlignmentPivotRequest n i) :=
  (alignmentCanonicalRequests n i).map
    (alignmentFutureRequest (alignmentPlannedFutureProducts later))

noncomputable def selectedAlignmentScheduleAux {n : ℕ} (r s : ℕ) :
    List (Fin n) → List (AlignmentPlannedPivot n)
  | [] => []
  | i :: pivots =>
    let later := selectedAlignmentScheduleAux r s pivots
    ⟨i, selectedAlignmentCosetPlan (κ := Fin r) s
      (selectedAlignmentScheduleRequests later i)⟩ :: later

noncomputable def selectedAlignmentSchedule (n r s : ℕ) : List (AlignmentPlannedPivot n) :=
  selectedAlignmentScheduleAux r s (List.finRange n)

noncomputable def SelectedAlignmentScheduleExact {n : ℕ} (r s : ℕ) :
    List (AlignmentPlannedPivot n) → Prop
  | [] => True
  | p :: later => p.plan = selectedAlignmentCosetPlan (κ := Fin r) s
      (selectedAlignmentScheduleRequests later p.pivot) ∧ SelectedAlignmentScheduleExact r s later

theorem selected_alignment_schedule_aux_exact {n : ℕ} (r s : ℕ) (pivots : List (Fin n)) :
    SelectedAlignmentScheduleExact r s (selectedAlignmentScheduleAux r s pivots) := by
  induction pivots with
  | nil => trivial
  | cons i pivots ih => exact ⟨rfl, ih⟩

theorem selected_alignment_schedule_aux_pivots {n : ℕ} (r s : ℕ) (pivots : List (Fin n)) :
    (selectedAlignmentScheduleAux r s pivots).map AlignmentPlannedPivot.pivot = pivots := by
  induction pivots with
  | nil => rfl
  | cons i pivots ih => exact congrArg (List.cons i) ih

theorem selected_alignment_schedule_exact (n r s : ℕ) :
    SelectedAlignmentScheduleExact r s (selectedAlignmentSchedule n r s) :=
  selected_alignment_schedule_aux_exact r s _

theorem selected_alignment_schedule_cover (n r s : ℕ) :
    (selectedAlignmentSchedule n r s).map AlignmentPlannedPivot.pivot = List.finRange n :=
  selected_alignment_schedule_aux_pivots r s _

theorem selected_alignment_schedule_length (n r s : ℕ) :
    (selectedAlignmentSchedule n r s).length = n := by
  have h := congrArg List.length (selected_alignment_schedule_cover n r s)
  simpa using h

theorem SelectedAlignmentScheduleExact.suffix {n r s : ℕ}
    (earlier later : List (AlignmentPlannedPivot n))
    (h : SelectedAlignmentScheduleExact r s (earlier ++ later)) :
    SelectedAlignmentScheduleExact r s later := by
  induction earlier with
  | nil => exact h
  | cons p earlier ih => exact ih h.2

theorem SelectedAlignmentScheduleExact.plan {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (h : SelectedAlignmentScheduleExact r s (earlier ++ p :: later)) :
    p.plan = selectedAlignmentCosetPlan (κ := Fin r) s
      (selectedAlignmentScheduleRequests later p.pivot) :=
  (h.suffix earlier (p :: later)).1

theorem SelectedAlignmentScheduleExact.fits {n r s : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} (h : SelectedAlignmentScheduleExact r s schedule) :
    alignmentAllPivotFits (alignmentCanonicalRequests n) schedule := by
  induction schedule with
  | nil => trivial
  | cons p later ih =>
    refine ⟨?_, ih h.2⟩
    rw [h.1]
    exact selected_alignment_coset_plan_fits s _

theorem SelectedAlignmentScheduleExact.works {n r s : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} (h : SelectedAlignmentScheduleExact r s schedule) :
    ∀ p ∈ schedule, ∀ stage ∈ p.plan,
      AlignmentPivotStageWorks.{0,0} (s+1) (Fin r → Bool) stage := by
  induction schedule with
  | nil => simp
  | cons p later ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [h.1]
      exact selected_alignment_coset_plan_works s _
    · exact ih h.2 q hq

theorem SelectedAlignmentScheduleExact.positive {n r s : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} (h : SelectedAlignmentScheduleExact r s schedule) :
    ∀ p ∈ schedule, ∀ stage ∈ p.plan, ∀ c ∈ stage.choices, 0 < c.1 :=
  fun p hp stage hs => (h.works p hp stage hs).1

theorem SelectedAlignmentScheduleExact.routes_nonempty {n r s : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} (h : SelectedAlignmentScheduleExact r s schedule) :
    ∀ p ∈ schedule, (principalPivotRoutes p.plan).Nonempty := by
  induction schedule with
  | nil => simp
  | cons p later ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [h.1]
      exact selected_alignment_coset_routes_nonempty s _
    · exact ih h.2 q hq

theorem selected_alignment_schedule_requests_own {n : ℕ}
    (later : List (AlignmentPlannedPivot n)) (i : Fin n) :
    ∀ request ∈ selectedAlignmentScheduleRequests later i, ∀ word ∈ request.words,
      ∀ l ∈ word, l.1.targetTail = request.tail := by
  intro request hr
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
  exact alignment_future_request_words_own_target _ original
    (alignment_canonical_request_words_own_target original ho)

theorem selected_alignment_schedule_requests_positive {n r s : ℕ}
    (later : List (AlignmentPlannedPivot n)) (h : SelectedAlignmentScheduleExact r s later)
    (i : Fin n) : ∀ request ∈ selectedAlignmentScheduleRequests later i,
      ∀ a ∈ request.leading, 0 < a := by
  intro request hr
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
  exact alignmentFutureRequest_leading_positive _ original
    (alignmentPlannedFutureProducts_positive later h.positive)
    (alignmentCanonicalRequests_leading_positive n i original ho)

/-- Every route's actual final scale belongs to the precise forward frontier. -/
theorem selected_alignment_route_scale_mem {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (hr : route ∈ principalPivotRoutes plan) :
    (principalPivotRouteValue q₀ L plan b route).1 ∈
      alignmentScaleFrontier i (alignmentForwardOptions plan) {b} := by
  induction plan generalizing route with
  | nil => exact Finset.mem_singleton_self _
  | cons stage earlier ih =>
    obtain ⟨⟨old, choice⟩, hp, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hold, hchoice⟩ := Finset.mem_product.mp hp
    rw [alignmentForwardOptions_cons, alignmentScaleFrontier_append]
    exact alignmentScaleStep_contains i (alignmentPivotStageOptions stage) _ _
      (ih old hold) choice hchoice

theorem selected_alignment_planned_multipliers_nonempty {n : ℕ}
    (p : AlignmentPlannedPivot n) (h : (principalPivotRoutes p.plan).Nonempty) :
    (alignmentPlannedMultipliers p).Nonempty := by
  obtain ⟨route, hr⟩ := h
  exact ⟨_, selected_alignment_route_scale_mem 1 (fun _ => (1 : Unit)) p.plan
    (fun _ => 1) route hr⟩

noncomputable def selectedAlignmentScheduleIncoming {n : ℕ} :
    List (AlignmentPlannedPivot n) → Finset (Fin n → ℚ) → Finset (Fin n → ℚ)
  | [], incoming => incoming
  | p :: later, incoming =>
    selectedAlignmentScheduleIncoming later (alignmentScheduleStep p incoming)

theorem selected_alignment_schedule_incoming_positive {n : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hp : ∀ p ∈ earlier, ∀ stage ∈ p.plan, ∀ c ∈ stage.choices, 0 < c.1) :
    ∀ b ∈ selectedAlignmentScheduleIncoming earlier incoming, ∀ j, 0 < b j := by
  induction earlier generalizing incoming with
  | nil => exact hin
  | cons p earlier ih =>
    exact ih _
      (alignmentScheduleStep_positive p incoming hin (hp p List.mem_cons_self))
      (fun p' h => hp p' (List.mem_cons_of_mem p h))

theorem selected_alignment_schedule_incoming_nonempty {n : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ))
    (hin : incoming.Nonempty)
    (hp : ∀ p ∈ earlier, (principalPivotRoutes p.plan).Nonempty) :
    (selectedAlignmentScheduleIncoming earlier incoming).Nonempty := by
  induction earlier generalizing incoming with
  | nil => exact hin
  | cons p earlier ih =>
    apply ih _ _ (fun p' h => hp p' (List.mem_cons_of_mem p h))
    obtain ⟨b, hb⟩ := hin
    obtain ⟨d, hd⟩ := selected_alignment_planned_multipliers_nonempty p (hp p List.mem_cons_self)
    exact ⟨_, alignmentScaleSetProduct_contains _ _ b d hb hd⟩

theorem selected_alignment_schedule_suffix_states {n : ℕ}
    (earlier later : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    alignmentScheduleStates later (selectedAlignmentScheduleIncoming earlier incoming) ⊆
      alignmentScheduleStates (earlier ++ later) incoming := by
  induction earlier generalizing incoming with
  | nil => exact Finset.Subset.refl _
  | cons p earlier ih =>
    exact Finset.Subset.trans (ih _) (alignmentScheduleStates_tail p (earlier ++ later) incoming)

theorem selected_alignment_schedule_prefix_incoming {n : ℕ}
    (earlier later : List (AlignmentPlannedPivot n)) (incoming : Finset (Fin n → ℚ)) :
    selectedAlignmentScheduleIncoming earlier incoming ⊆
      alignmentScheduleStates (earlier ++ later) incoming :=
  Finset.Subset.trans (alignmentScheduleStates_contains_incoming _ _)
    (selected_alignment_schedule_suffix_states earlier later incoming)

theorem selected_alignment_schedule_future_nonempty {n : ℕ}
    (schedule : List (AlignmentPlannedPivot n))
    (h : ∀ p ∈ schedule, (principalPivotRoutes p.plan).Nonempty) :
    (alignmentPlannedFutureProducts schedule).Nonempty := by
  induction schedule with
  | nil => exact Finset.singleton_nonempty _
  | cons p later ih =>
    obtain ⟨b, hb⟩ := selected_alignment_planned_multipliers_nonempty p (h p List.mem_cons_self)
    obtain ⟨d, hd⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    exact ⟨_, alignmentScaleSetProduct_contains _ _ b d hb hd⟩

theorem selected_alignment_schedule_final_nonempty {n r s : ℕ}
    {schedule : List (AlignmentPlannedPivot n)} (h : SelectedAlignmentScheduleExact r s schedule) :
    (alignmentScheduleFinalScales schedule {fun _ => 1}).Nonempty := by
  obtain ⟨d, hd⟩ := selected_alignment_schedule_future_nonempty schedule h.routes_nonempty
  exact ⟨_, alignmentScheduleFinalScales_contains schedule _ _ d
    (Finset.mem_singleton_self _) hd⟩

end Hindman168
