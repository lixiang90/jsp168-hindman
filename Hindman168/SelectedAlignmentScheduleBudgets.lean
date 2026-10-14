import Hindman168.SelectedAlignmentSchedulePlans

/-! One finite, positive scale family and one positive denominator serve
all stages, all actual route factors, and the final canonical comparisons.
Neither depends on thresholds or represented functions. -/
namespace Hindman168
open scoped Classical

noncomputable def selectedAlignmentScheduleStates (n r s : ℕ) : Finset (Fin n → ℚ) :=
  alignmentScheduleStates (selectedAlignmentSchedule n r s) {fun _ => 1} ∪
    alignmentScheduleFinalScales (selectedAlignmentSchedule n r s) {fun _ => 1}

noncomputable def selectedAlignmentScheduleFinal (n r s : ℕ) : Finset (Fin n → ℚ) :=
  alignmentScheduleFinalScales (selectedAlignmentSchedule n r s) {fun _ => 1}

noncomputable def selectedAlignmentScheduleLocalScalars {n : ℕ} :
    List (AlignmentPlannedPivot n) → Finset (Fin n → ℚ) → Finset ℚ
  | [], _ => ∅
  | p :: later, states =>
    states.biUnion (fun b =>
      (alignmentScheduleLetters (selectedAlignmentScheduleRequests later) p).image
        (alignmentLetterScalar b)) ∪ selectedAlignmentScheduleLocalScalars later states

noncomputable def selectedAlignmentScheduleFinalScalars {n : ℕ}
    (states : Finset (Fin n → ℚ)) : Finset ℚ :=
  states.biUnion fun b => Finset.univ.biUnion fun i : Fin n =>
    (alignmentCanonicalPairs n i).toFinset.image fun p =>
      finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)

noncomputable def selectedAlignmentScheduleScalarBudget (n r s : ℕ) : Finset ℚ :=
  selectedAlignmentScheduleLocalScalars (selectedAlignmentSchedule n r s)
    (selectedAlignmentScheduleStates n r s) ∪
  alignmentScheduleScalars (alignmentCanonicalRequests n) (selectedAlignmentSchedule n r s)
    (selectedAlignmentScheduleStates n r s) ∪
  selectedAlignmentScheduleFinalScalars (selectedAlignmentScheduleFinal n r s)

noncomputable def selectedAlignmentScheduleClearing (n r s : ℕ) : ℕ :=
  Classical.choose (rational_finite_family_integer_multiplier
    (selectedAlignmentScheduleScalarBudget n r s) id)

theorem selected_alignment_schedule_clearing_pos (n r s : ℕ) :
    0 < selectedAlignmentScheduleClearing n r s :=
  (Classical.choose_spec (rational_finite_family_integer_multiplier
    (selectedAlignmentScheduleScalarBudget n r s) id)).1

theorem selected_alignment_schedule_clearing_scalar (n r s : ℕ) (a : ℚ)
    (ha : a ∈ selectedAlignmentScheduleScalarBudget n r s) :
    (selectedAlignmentScheduleClearing n r s : ℚ) * a ∈ (Int.castRingHom ℚ).range :=
  (Classical.choose_spec (rational_finite_family_integer_multiplier
    (selectedAlignmentScheduleScalarBudget n r s) id)).2 a ha

theorem selected_alignment_schedule_local_scalar_mem {n : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n)) (states : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ states)
    (l : AlignmentAddingPair n p.pivot × ℚ)
    (hl : l ∈ alignmentScheduleLetters (selectedAlignmentScheduleRequests later) p) :
    alignmentLetterScalar b l ∈ selectedAlignmentScheduleLocalScalars (earlier ++ p :: later) states := by
  induction earlier with
  | nil =>
    exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩)
  | cons q earlier ih => exact Finset.mem_union_right _ ih

theorem selected_alignment_schedule_local_clearing {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later)
    (b : Fin n → ℚ) (hb : b ∈ selectedAlignmentScheduleStates n r s)
    (l : AlignmentAddingPair n p.pivot × ℚ)
    (hl : l ∈ alignmentScheduleLetters (selectedAlignmentScheduleRequests later) p) :
    (selectedAlignmentScheduleClearing n r s : ℚ) * alignmentLetterScalar b l ∈
      (Int.castRingHom ℚ).range := by
  apply selected_alignment_schedule_clearing_scalar n r s
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [hs]
  exact selected_alignment_schedule_local_scalar_mem earlier p later _ b hb l hl

theorem selected_alignment_schedule_denominators {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later) :
    ∀ stage ∈ p.plan, ∀ b ∈ alignmentAllScaleStates p.pivot (alignmentForwardOptions p.plan)
      (selectedAlignmentScheduleIncoming earlier {fun _ => 1}),
      ∀ l ∈ alignmentWordLetters stage.target.words,
      (selectedAlignmentScheduleClearing n r s : ℚ) * alignmentLetterScalar b l ∈
        (Int.castRingHom ℚ).range := by
  intro stage hstage b hb l hl
  apply selected_alignment_schedule_local_clearing earlier p later hs b _ l
    (alignmentScheduleLetters_stage _ p stage hstage l hl)
  apply Finset.mem_union_left
  rw [hs]
  exact selected_alignment_schedule_suffix_states earlier (p :: later) _
    (alignmentScheduleStates_head p later _ hb)

theorem selected_alignment_schedule_final_denominators (n r s : ℕ) :
    ∀ b ∈ selectedAlignmentScheduleFinal n r s, ∀ i, ∀ p : AlignmentAddingPair n i,
      (selectedAlignmentScheduleClearing n r s : ℚ) *
        (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
          finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range := by
  intro b hb i p
  apply selected_alignment_schedule_clearing_scalar n r s
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr (alignmentCanonicalPairs_contains p), rfl⟩⟩⟩

noncomputable def selectedAlignmentSchedulePaletteIndices {n : ℕ} :
    List (AlignmentPlannedPivot n) → Finset (Fin n → ℚ) → Finset ℚ
  | [], _ => ∅
  | p :: later, states =>
    states.biUnion (fun b =>
      (alignmentPlannedPaletteBudget (selectedAlignmentScheduleRequests later) p).image
        (fun ba => ba.2 * finiteScaleBlockProduct b ba.1)) ∪
      selectedAlignmentSchedulePaletteIndices later states

noncomputable def selectedAlignmentScheduleScales (n r s : ℕ) : Finset ℚ :=
  finiteScaleProductClosure (selectedAlignmentScheduleFinal n r s)
    (selectedAlignmentSchedulePaletteIndices (selectedAlignmentSchedule n r s)
      (selectedAlignmentScheduleStates n r s))

theorem selected_alignment_schedule_final_positive (n r s : ℕ) :
    ∀ b ∈ selectedAlignmentScheduleFinal n r s, ∀ j, 0 < b j :=
  alignmentScheduleFinalScales_positive _ _
    (by intro b hb; obtain rfl := Finset.mem_singleton.mp hb; exact fun _ => zero_lt_one)
    (selected_alignment_schedule_exact n r s).positive

theorem selected_alignment_schedule_states_positive (n r s : ℕ) :
    ∀ b ∈ selectedAlignmentScheduleStates n r s, ∀ j, 0 < b j := by
  intro b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact alignmentScheduleStates_positive _ _
      (by intro c hc; obtain rfl := Finset.mem_singleton.mp hc; exact fun _ => zero_lt_one)
      (selected_alignment_schedule_exact n r s).positive b hb
  · exact selected_alignment_schedule_final_positive n r s b hb

theorem selected_alignment_schedule_palette_positive {n r s : ℕ}
    (schedule : List (AlignmentPlannedPivot n)) (hex : SelectedAlignmentScheduleExact r s schedule)
    (states : Finset (Fin n → ℚ)) (hstates : ∀ b ∈ states, ∀ j, 0 < b j) :
    ∀ a ∈ selectedAlignmentSchedulePaletteIndices schedule states, 0 < a := by
  induction schedule with
  | nil => simp [selectedAlignmentSchedulePaletteIndices]
  | cons p later ih =>
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨b, hb, hbudget⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ba, hba, rfl⟩ := Finset.mem_image.mp hbudget
      apply mul_pos _ (finiteScaleBlockProduct_positive b (hstates b hb) _)
      apply alignmentPlannedPaletteBudget_positive _ p _
        (selected_alignment_schedule_requests_positive later hex.2 p.pivot) ba hba
      apply alignmentBackwardPlanFits_leading_positive p.plan _ _
        (hex.positive p List.mem_cons_self)
        (selected_alignment_schedule_requests_positive later hex.2 p.pivot)
      rw [hex.1]
      exact selected_alignment_coset_plan_fits s _
    · exact ih hex.2 a ha

theorem selected_alignment_schedule_scales_positive (n r s : ℕ) :
    ∀ a ∈ selectedAlignmentScheduleScales n r s, 0 < a :=
  finiteScaleProductClosure_positive _ _ (selected_alignment_schedule_final_positive n r s)
    (selected_alignment_schedule_palette_positive _ (selected_alignment_schedule_exact n r s) _
      (selected_alignment_schedule_states_positive n r s))

theorem selected_alignment_schedule_scales_closed (n r s : ℕ) :
    FiniteScaleClosure (selectedAlignmentScheduleFinal n r s) (selectedAlignmentScheduleScales n r s) :=
  finiteScaleProductClosure_closed _ _

theorem selected_alignment_schedule_palette_mem {n : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n)) (states : Finset (Fin n → ℚ))
    (b : Fin n → ℚ) (hb : b ∈ states) (ba : Finset (Fin n) × ℚ)
    (hba : ba ∈ alignmentPlannedPaletteBudget (selectedAlignmentScheduleRequests later) p) :
    ba.2 * finiteScaleBlockProduct b ba.1 ∈
      selectedAlignmentSchedulePaletteIndices (earlier ++ p :: later) states := by
  induction earlier with
  | nil =>
    exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨ba, hba, rfl⟩⟩)
  | cons q earlier ih => exact Finset.mem_union_right _ ih

theorem selected_alignment_schedule_scale_mem {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later)
    (b : Fin n → ℚ) (hb : b ∈ selectedAlignmentScheduleStates n r s)
    (ba : Finset (Fin n) × ℚ)
    (hba : ba ∈ alignmentPlannedPaletteBudget (selectedAlignmentScheduleRequests later) p) :
    ba.2 * finiteScaleBlockProduct b ba.1 ∈ selectedAlignmentScheduleScales n r s := by
  apply finiteScaleProductClosure_contains
  rw [hs]
  exact selected_alignment_schedule_palette_mem earlier p later _ b hb ba hba

theorem selected_alignment_schedule_stage_scale_mem {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later)
    (stage : AlignmentPivotStage n p.pivot) (hstage : stage ∈ p.plan)
    (b : Fin n → ℚ) (hb : b ∈ selectedAlignmentScheduleStates n r s)
    (a : ℚ) (ha : a ∈ stage.target.leading) :
    a * finiteScaleBlockProduct b (insert p.pivot stage.target.tail) ∈
      selectedAlignmentScheduleScales n r s :=
  selected_alignment_schedule_scale_mem earlier p later hs b hb _
    (alignmentPlannedPaletteBudget_stage _ p stage hstage a ha)

/-- The literal scale component of every route factor lies in the family
fixed before the represented model is selected. -/
theorem selected_alignment_schedule_catalogue_scale_mem {n r s : ℕ}
    (earlier : List (AlignmentPlannedPivot n)) (p : AlignmentPlannedPivot n)
    (later : List (AlignmentPlannedPivot n))
    (hs : selectedAlignmentSchedule n r s = earlier ++ p :: later)
    (q₀ : ℕ)
    (ν : AlignmentJointRouteFactor p.pivot (Fin r))
    (hν : ν ∈ alignmentJointRouteFactorCatalogue (Fin r) q₀ p.plan
      (selectedAlignmentScheduleIncoming earlier {fun _ => 1})
      (selectedAlignmentScheduleRequests later p.pivot)) :
    ν.2.1 ∈ selectedAlignmentScheduleScales n r s := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  obtain ⟨b, hb, hroute⟩ := Finset.mem_biUnion.mp hν
  obtain ⟨route, hr, hrequest⟩ := Finset.mem_biUnion.mp hroute
  obtain ⟨request, hrequest, hlead⟩ := Finset.mem_biUnion.mp hrequest
  obtain ⟨a, ha, hcolor⟩ := Finset.mem_biUnion.mp hlead
  obtain ⟨c, _, hfactor⟩ := Finset.mem_biUnion.mp hcolor
  have har : (alignmentJointRouteArithmetic q₀ p.plan b route).1 ∈
      selectedAlignmentScheduleStates n r s := by
    apply Finset.mem_union_left
    rw [hs]
    apply selected_alignment_schedule_suffix_states earlier (p :: later) _
    apply alignmentScheduleStates_head
    apply alignmentScaleFrontier_subset_all
    apply alignmentScaleFrontier_mono _ _ _ _ (Finset.singleton_subset_iff.mpr hb)
    exact selected_alignment_route_scale_mem q₀ _ p.plan b route hr
  have hscale := selected_alignment_schedule_scale_mem earlier p later hs _ har _
    (alignmentPlannedPaletteBudget_request _ p request (List.mem_toFinset.mp hrequest) a ha)
  rcases Finset.mem_union.mp hfactor with hfactor | hfactor
  · obtain rfl := Finset.mem_singleton.mp hfactor
    exact hscale
  · obtain ⟨word, _, rfl⟩ := Finset.mem_image.mp hfactor
    exact hscale

end Hindman168
