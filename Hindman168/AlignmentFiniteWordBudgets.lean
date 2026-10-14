import Hindman168.AlignmentGlobalPaletteScales
import Hindman168.AlignmentAuxiliaryTerminalSlots

/-! The complete canonical finite-word construction has a positive
prediction scale list and actual finite auxiliary visit tables. -/

namespace Hindman168
universe u v
open scoped Classical

theorem alignment_finite_word_budgets {n : ℕ} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s) :
    ∃ schedule : List (AlignmentPlannedPivot n),
      schedule.map AlignmentPlannedPivot.pivot = List.finRange n ∧
      alignmentAllPivotFits (alignmentCanonicalRequests n) schedule ∧
      (∀ planned ∈ schedule, ∀ stage ∈ planned.plan,
        AlignmentPivotStageWorks.{u, v} s Color stage) ∧
      ∃ A : Finset ℚ, A = alignmentSchedulePredictionScales (alignmentCanonicalRequests n)
        schedule {fun _ => 1} ∧ (∀ a ∈ A, 0 < a) ∧
      FiniteScaleClosure (alignmentScheduleFinalScales schedule {fun _ => 1}) A ∧
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
          ∀ position : ∀ i, X i → AlignmentAddingPair n i → ℤ,
            (∀ i e x f, position i (L i e • x) f = position i x f + if f = e then 1 else 0) →
            (∀ i, position i (centers i) = 0) →
            alignmentScheduleSlotsRealizes G X q₀
              (alignmentScheduleStates schedule {fun _ => 1} ∪
                alignmentScheduleFinalScales schedule {fun _ => 1})
              L palette (alignmentCanonicalRequests n) centers position
              schedule (fun _ => 1) final := by
  obtain ⟨schedule, hpivots, hfit, hworks, huniform⟩ := alignment_uniform_schedule.{u, v}
    (Color := Color) s hrec (alignmentCanonicalRequests n) (List.finRange n)
  have hchoices : ∀ planned ∈ schedule, ∀ stage ∈ planned.plan, ∀ p ∈ stage.choices, 0 < p.1 :=
    fun planned hp stage hs => (hworks planned hp stage hs).1
  let A := alignmentSchedulePredictionScales (alignmentCanonicalRequests n) schedule {fun _ => 1}
  have hA : ∀ a ∈ A, 0 < a := by
    apply alignmentSchedulePredictionScales_positive _ schedule _ hfit hchoices
      (alignmentCanonicalRequests_leading_positive n)
    intro b hb
    have h : b = fun _ => 1 := Finset.mem_singleton.mp hb
    subst b
    intro j
    exact zero_lt_one
  obtain ⟨q₀, hq, hint, hexec⟩ := huniform {fun _ => 1}
  refine ⟨schedule, hpivots, hfit, hworks, A, rfl, hA,
    alignmentSchedulePredictionScales_closed _ schedule _, q₀, hq, hint, ?_⟩
  intro G X _ _ L hG palette centers
  obtain ⟨final, hf, hstates, hpos, hreal⟩ := hexec G X L hG palette centers
    (fun _ => 1) (Finset.mem_singleton_self _) (fun _ => zero_lt_one)
  refine ⟨final, hf, hstates, hpos, hreal, ?_⟩
  intro position hL hzero
  exact alignmentScheduleRealizes_slots q₀ L palette (alignmentCanonicalRequests n) centers
    position hL hzero schedule {fun _ => 1} _ Finset.subset_union_left _ final
    (Finset.mem_singleton_self _) (Finset.mem_union_right _ hf) hreal

end Hindman168
