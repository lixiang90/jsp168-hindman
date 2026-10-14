import Hindman168.AlignmentScheduleExecution
import Hindman168.AlignmentTerminalWords

/-! All pairs and targets of the original finite-word problem are now
enumerated from n alone; no user-supplied request family is needed. -/

namespace Hindman168
universe u v
open scoped Classical

theorem alignmentAddingPair_fields_injective {n : ℕ} {i : Fin n} :
    Function.Injective (fun e : AlignmentAddingPair n i =>
      (e.sourceTail, e.targetTail, e.sourcePivot)) := by
  intro e f h
  cases e
  cases f
  cases h
  rfl

@[reducible]
noncomputable def alignmentAddingPairFintype (n : ℕ) (i : Fin n) :
    Fintype (AlignmentAddingPair n i) :=
  Fintype.ofInjective (fun e => (e.sourceTail, e.targetTail, e.sourcePivot))
    alignmentAddingPair_fields_injective

noncomputable def alignmentCanonicalPairs (n : ℕ) (i : Fin n) : List (AlignmentAddingPair n i) :=
  letI := alignmentAddingPairFintype n i
  (Finset.univ : Finset (AlignmentAddingPair n i)).toList

theorem alignmentCanonicalPairs_contains {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    e ∈ alignmentCanonicalPairs n i := by
  simp only [alignmentCanonicalPairs, Finset.mem_toList, Finset.mem_univ]

theorem alignmentCanonicalPairs_nodup (n : ℕ) (i : Fin n) :
    (alignmentCanonicalPairs n i).Nodup := Finset.nodup_toList _

noncomputable def alignmentCanonicalTargetTails (n : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  (alignmentCanonicalPairs n i).toFinset.image AlignmentAddingPair.targetTail

theorem alignmentCanonicalTargetTails_contains {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) : e.targetTail ∈ alignmentCanonicalTargetTails n i :=
  Finset.mem_image.mpr ⟨e, List.mem_toFinset.mpr (alignmentCanonicalPairs_contains e), rfl⟩

theorem alignmentCanonicalTargetTails_before {n : ℕ} {i : Fin n}
    (T : Finset (Fin n)) (hT : T ∈ alignmentCanonicalTargetTails n i) : ∀ j ∈ T, j < i := by
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hT
  exact alignmentPair_target_before e

noncomputable def alignmentCanonicalTargetPairs (n : ℕ) (i : Fin n)
    (T : Finset (Fin n)) : List (AlignmentAddingPair n i) :=
  (alignmentCanonicalPairs n i).filter (fun e => e.targetTail = T)

theorem alignmentCanonicalTargetPairs_contains {n : ℕ} {i : Fin n}
    (T : Finset (Fin n)) (e : AlignmentAddingPair n i) :
    e ∈ alignmentCanonicalTargetPairs n i T ↔ e.targetTail = T := by
  simp only [alignmentCanonicalTargetPairs, List.mem_filter, decide_eq_true_eq,
    alignmentCanonicalPairs_contains, true_and]

theorem alignmentCanonicalTargetPairs_nodup (n : ℕ) (i : Fin n) (T : Finset (Fin n)) :
    (alignmentCanonicalTargetPairs n i T).Nodup := (alignmentCanonicalPairs_nodup n i).filter _

noncomputable def alignmentCanonicalRequest {n : ℕ} {i : Fin n}
    (T : {T // T ∈ alignmentCanonicalTargetTails n i}) : AlignmentPivotRequest n i :=
  alignmentTerminalRequest T.val (alignmentCanonicalTargetTails_before T.val T.property)
    (alignmentCanonicalTargetPairs n i T.val)

noncomputable def alignmentCanonicalRequests (n : ℕ) (i : Fin n) :
    List (AlignmentPivotRequest n i) :=
  (alignmentCanonicalTargetTails n i).attach.toList.map alignmentCanonicalRequest

theorem alignmentCanonicalRequests_contains {n : ℕ} {i : Fin n}
    (T : {T // T ∈ alignmentCanonicalTargetTails n i}) :
    alignmentCanonicalRequest T ∈ alignmentCanonicalRequests n i :=
  List.mem_map.mpr ⟨T, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩

theorem alignmentCanonicalRequests_comparison {n : ℕ} {i : Fin n}
    {G X Color : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (palette : Finset (Fin n) → ℚ → X → Color) (y : X)
    (hreq : ∀ request ∈ alignmentCanonicalRequests n i,
      alignmentPivotRequestHolds q₀ b L palette y request)
    (T : Finset (Fin n)) (hT : T ∈ alignmentCanonicalTargetTails n i)
    (selected : List (AlignmentAddingPair n i))
    (hselected : selected.Sublist (alignmentCanonicalTargetPairs n i T)) :
    palette (insert i T) (finiteScaleBlockProduct b (insert i T)) y =
      palette (insert i T) (finiteScaleBlockProduct b (insert i T))
        (alignmentWordValue q₀ b L (selected.map (fun e => (e, (1 : ℚ)))) • y) := by
  have h := hreq _ (alignmentCanonicalRequests_contains ⟨T, hT⟩)
  simpa only [alignmentCanonicalRequest, alignmentTerminalRequest, one_mul] using
    h 1 (Finset.mem_singleton_self 1) _ (alignmentTerminalWords_contains _ selected hselected)

theorem alignment_canonical_finite_word_plan {n : ℕ} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s) :
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
  obtain ⟨schedule, hpivots, _, _, hschedule⟩ := alignment_uniform_schedule.{u, v}
    (Color := Color) s hrec (alignmentCanonicalRequests n) (List.finRange n)
  obtain ⟨q₀, hq, hint, hexec⟩ := hschedule {fun _ => 1}
  refine ⟨schedule, hpivots, q₀, hq, hint, ?_⟩
  intro G X _ _ L hG palette centers
  obtain ⟨final, hf, hstates, hpos, hreal⟩ :=
    hexec G X L hG palette centers (fun _ => 1) (Finset.mem_singleton_self _) (fun _ => zero_lt_one)
  refine ⟨final, hf, hstates, hpos, hreal, ?_⟩
  intro i
  have hi : i ∈ schedule.map AlignmentPlannedPivot.pivot := by
    rw [hpivots]
    exact List.mem_finRange i
  obtain ⟨planned, hp, heq⟩ := List.mem_map.mp hi
  obtain ⟨y, hy⟩ := alignmentScheduleRealizes_comparisons q₀ L palette
    (alignmentCanonicalRequests n) centers schedule _ final hreal planned hp
  subst i
  refine ⟨y, ?_⟩
  intro T hT selected hselected
  exact alignmentCanonicalRequests_comparison q₀ final (L planned.pivot)
    (palette planned.pivot) y hy T hT selected hselected

end Hindman168
