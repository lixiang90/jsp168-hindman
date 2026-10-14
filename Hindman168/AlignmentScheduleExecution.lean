import Hindman168.AlignmentScheduleDenominators

/-! The backward schedule executes in order at independent pivot centers.
The recursive trace keeps each chosen center fixed in its final comparisons. -/

namespace Hindman168
universe u v
open scoped Classical

def alignmentScheduleRealizes {n : ℕ} {Color : Type}
    (G : Fin n → Type u) (X : Fin n → Type v)
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color)
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (centers : ∀ i, X i) :
    List (AlignmentPlannedPivot n) → (Fin n → ℚ) → (Fin n → ℚ) → Prop
  | [], b, final => final = b
  | planned :: later, b, final => ∃ c y,
    alignmentPivotReachable q₀ (L planned.pivot) planned.plan b (centers planned.pivot) c y ∧
    (∀ request ∈ requests planned.pivot,
      alignmentPivotRequestHolds q₀ final (L planned.pivot) (palette planned.pivot) y request) ∧
    alignmentScheduleRealizes G X q₀ L palette requests centers later c final

theorem alignmentScheduleRealizes_comparisons {n : ℕ} {Color : Type}
    {G : Fin n → Type u} {X : Fin n → Type v}
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color)
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (centers : ∀ i, X i)
    (schedule : List (AlignmentPlannedPivot n)) (b final : Fin n → ℚ)
    (hreal : alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final) :
    ∀ planned ∈ schedule, ∃ y : X planned.pivot, ∀ request ∈ requests planned.pivot,
      alignmentPivotRequestHolds q₀ final (L planned.pivot) (palette planned.pivot) y request := by
  induction schedule generalizing b with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons planned later ih =>
    obtain ⟨c, y, _, hreq, htail⟩ := hreal
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨y, hreq⟩
    · exact ih c htail p hp

theorem alignment_schedule_execute {n : ℕ} {Color : Type}
    {G : Fin n → Type u} {X : Fin n → Type v}
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (s : ℕ) (schedule : List (AlignmentPlannedPivot n))
    (requests : ∀ i, List (AlignmentPivotRequest n i))
    (hfit : alignmentAllPivotFits requests schedule)
    (hworks : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
      AlignmentPivotStageWorks.{u, v} s Color stage)
    (incoming : Finset (Fin n → ℚ)) (q₀ : ℕ)
    (hint : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
      ∀ b ∈ alignmentScheduleStates schedule incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (L : ∀ i, AlignmentAddingPair n i → G i)
    (hG : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥)
    (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color) (centers : ∀ i, X i)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) :
    ∃ final ∈ alignmentScheduleStates schedule incoming,
      ∃ d ∈ alignmentPlannedFutureProducts schedule,
        final = alignmentMultiplyScales b d ∧ (∀ j, 0 < final j) ∧
          alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final := by
  induction schedule generalizing incoming b with
  | nil =>
    refine ⟨b, hb, fun _ => 1, Finset.mem_singleton_self _, ?_, hpos, rfl⟩
    funext j
    exact (mul_one (b j)).symm
  | cons planned later ih =>
    obtain ⟨hhead, htail⟩ := hfit
    have hwhead := hworks planned List.mem_cons_self
    have hsingleton : ({b} : Finset (Fin n → ℚ)) ⊆ incoming :=
      Finset.singleton_subset_iff.mpr hb
    have hihead : ∀ stage ∈ planned.plan,
        ∀ c ∈ alignmentAllScaleStates planned.pivot (alignmentForwardOptions planned.plan) {b},
          ∀ l ∈ alignmentWordLetters stage.target.words,
            (q₀ : ℚ) * alignmentLetterScalar c l ∈ (Int.castRingHom ℚ).range := by
      intro stage hs c hc l hl
      exact hint planned List.mem_cons_self stage hs c
        (alignmentScheduleStates_head planned later incoming
          (alignmentAllScaleStates_mono _ _ _ _ hsingleton hc)) l hl
    obtain ⟨c, hc, y, hcpos, hreach, hrequests⟩ := alignment_pivot_plan_execute
      s planned.plan _ hhead hwhead {b} q₀ hihead (L planned.pivot) (hG planned.pivot)
      (palette planned.pivot) b (Finset.mem_singleton_self b) hpos (centers planned.pivot)
    have hcstep := alignmentScheduleStep_contains planned incoming b c hb hc
    have hwtail : ∀ p ∈ later, ∀ stage ∈ p.plan,
        AlignmentPivotStageWorks.{u, v} s Color stage :=
      fun p hp => hworks p (List.mem_cons_of_mem planned hp)
    have hitail : ∀ p ∈ later, ∀ stage ∈ p.plan,
        ∀ a ∈ alignmentScheduleStates later (alignmentScheduleStep planned incoming),
          ∀ l ∈ alignmentWordLetters stage.target.words,
            (q₀ : ℚ) * alignmentLetterScalar a l ∈ (Int.castRingHom ℚ).range :=
      fun p hp stage hs a ha => hint p (List.mem_cons_of_mem planned hp) stage hs a
        (alignmentScheduleStates_tail planned later incoming ha)
    obtain ⟨final, hf, d, hd, hfd, hfpos, hreal⟩ :=
      ih htail hwtail _ hitail c hcstep hcpos
    rw [alignmentScaleFrontier_singleton_factor] at hc
    obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hc
    refine ⟨final, alignmentScheduleStates_tail planned later incoming hf,
      alignmentMultiplyScales e d, alignmentScaleSetProduct_contains _ _ e d he hd,
      ?_, hfpos, c, y, hreach, ?_, hreal⟩
    · rw [hfd, ← hce]
      funext j
      exact mul_assoc (b j) (e j) (d j)
    · intro request hr
      rw [hfd]
      exact alignmentFutureRequest_transport q₀ c d (L planned.pivot)
        (palette planned.pivot) y (alignmentPlannedFutureProducts later) hd request
        (hrequests _ (List.mem_map.mpr ⟨request, hr, rfl⟩))

theorem alignment_uniform_schedule {n : ℕ} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (pivots : List (Fin n)) :
    ∃ schedule : List (AlignmentPlannedPivot n),
      schedule.map AlignmentPlannedPivot.pivot = pivots ∧
      alignmentAllPivotFits requests schedule ∧
      (∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
        AlignmentPivotStageWorks.{u, v} s Color stage) ∧
      ∀ incoming : Finset (Fin n → ℚ), ∃ q₀ : ℕ, 0 < q₀ ∧
      (∀ planned ∈ schedule,
        ∀ b ∈ alignmentScheduleStates schedule incoming ∪ alignmentScheduleFinalScales schedule incoming,
          ∀ l ∈ alignmentScheduleLetters requests planned,
            (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range) ∧
      ∀ (G : Fin n → Type u) (X : Fin n → Type v)
        [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
        (L : ∀ i, AlignmentAddingPair n i → G i)
        (_hG : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥)
        (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color) (centers : ∀ i, X i)
        (b : Fin n → ℚ) (_hb : b ∈ incoming) (_hpos : ∀ j, 0 < b j),
        ∃ final ∈ alignmentScheduleFinalScales schedule incoming,
          final ∈ alignmentScheduleStates schedule incoming ∧ (∀ j, 0 < final j) ∧
            alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final := by
  obtain ⟨schedule, hpivots, hfit, hworks⟩ :=
    alignment_all_pivot_plans_exist.{u, v} (Color := Color) s hrec requests pivots
  refine ⟨schedule, hpivots, hfit, hworks, ?_⟩
  intro incoming
  obtain ⟨q₀, hq, hint⟩ := alignment_schedule_finite_denominators requests schedule
    (alignmentScheduleStates schedule incoming ∪ alignmentScheduleFinalScales schedule incoming)
  refine ⟨q₀, hq, hint, ?_⟩
  intro G X _ _ L hG palette centers b hb hpos
  have hi : ∀ p ∈ schedule, ∀ stage ∈ p.plan,
      ∀ a ∈ alignmentScheduleStates schedule incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar a l ∈ (Int.castRingHom ℚ).range :=
    fun p hp stage hs a ha l hl => hint p hp a (Finset.mem_union_left _ ha) l
      (alignmentScheduleLetters_stage requests p stage hs l hl)
  obtain ⟨final, hf, d, hd, hfd, hfpos, hreal⟩ := alignment_schedule_execute
    s schedule requests hfit hworks incoming q₀ hi L hG palette centers b hb hpos
  refine ⟨final, ?_, hf, hfpos, hreal⟩
  rw [hfd]
  exact alignmentScheduleFinalScales_contains schedule incoming b d hb hd

end Hindman168
