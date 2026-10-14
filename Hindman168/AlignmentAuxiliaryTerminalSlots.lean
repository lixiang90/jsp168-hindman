import Hindman168.AlignmentAuxiliaryPlanSlots

/-! Jump visits and terminal-test visits share one prescribed finite slot
table at each pivot. The actual trace supplies the same successful center. -/

namespace Hindman168
universe u v
open scoped Classical

noncomputable def alignmentPlannedAuxiliarySlots {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (q₀ : ℕ)
    (B : Finset (Fin n → ℚ)) (planned : AlignmentPlannedPivot n) :
    Finset (AlignmentAddingPair n planned.pivot → ℤ) :=
  alignmentAuxiliaryPlanVisits q₀ B planned.plan {0} ∪
    (alignmentAuxiliaryFrontier q₀ B planned.plan {0}).biUnion (fun v => B.biUnion (fun b =>
      (requests planned.pivot).toFinset.biUnion (fun request => request.words.biUnion
        (fun w => (alignmentAuxiliaryWordVisits q₀ b w).image (v + ·)))))

def alignmentScheduleSlotsRealizes {n : ℕ} {Color : Type}
    (G : Fin n → Type u) (X : Fin n → Type v)
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) (L : ∀ i, AlignmentAddingPair n i → G i)
    (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color)
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (centers : ∀ i, X i)
    (position : ∀ i, X i → AlignmentAddingPair n i → ℤ) :
    List (AlignmentPlannedPivot n) → (Fin n → ℚ) → (Fin n → ℚ) → Prop
  | [], b, final => final = b
  | planned :: later, b, final => ∃ c y,
    alignmentPivotSlotsSafe q₀ (L planned.pivot) (position planned.pivot)
      (alignmentPlannedAuxiliarySlots requests q₀ B planned) planned.plan
      b (centers planned.pivot) c y ∧
    (∀ request ∈ requests planned.pivot,
      alignmentPivotRequestHolds q₀ final (L planned.pivot) (palette planned.pivot) y request) ∧
    (∀ request ∈ requests planned.pivot, ∀ w ∈ request.words,
      ∀ d ∈ alignmentAuxiliaryWordVisits q₀ final w,
        position planned.pivot y + d ∈ alignmentPlannedAuxiliarySlots requests q₀ B planned) ∧
    alignmentScheduleSlotsRealizes G X q₀ B L palette requests centers position later c final

theorem alignmentPlannedAuxiliarySlots_zero {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (q₀ : ℕ)
    (B : Finset (Fin n → ℚ)) (planned : AlignmentPlannedPivot n) :
    0 ∈ alignmentPlannedAuxiliarySlots requests q₀ B planned :=
  Finset.mem_union_left _ (alignmentAuxiliaryPlanVisits_contains_initial q₀ B planned.plan {0}
    (Finset.mem_singleton_self _))

theorem alignmentPlannedAuxiliarySlots_test {n : ℕ}
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (q₀ : ℕ)
    (B : Finset (Fin n → ℚ)) (planned : AlignmentPlannedPivot n)
    (v : AlignmentAddingPair n planned.pivot → ℤ)
    (hv : v ∈ alignmentAuxiliaryFrontier q₀ B planned.plan {0})
    (b : Fin n → ℚ) (hb : b ∈ B) (request : AlignmentPivotRequest n planned.pivot)
    (hr : request ∈ requests planned.pivot) (w : List (AlignmentAddingPair n planned.pivot × ℚ))
    (hw : w ∈ request.words) (d : AlignmentAddingPair n planned.pivot → ℤ)
    (hd : d ∈ alignmentAuxiliaryWordVisits q₀ b w) :
    v + d ∈ alignmentPlannedAuxiliarySlots requests q₀ B planned :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv,
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨request, List.mem_toFinset.mpr hr,
      Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩⟩⟩⟩)

theorem alignmentScheduleRealizes_slots {n : ℕ} {Color : Type}
    {G : Fin n → Type u} {X : Fin n → Type v}
    [∀ i, Group (G i)] [∀ i, MulAction (G i) (X i)]
    (q₀ : ℕ) (L : ∀ i, AlignmentAddingPair n i → G i)
    (palette : ∀ i, Finset (Fin n) → ℚ → X i → Color)
    (requests : ∀ i, List (AlignmentPivotRequest n i)) (centers : ∀ i, X i)
    (position : ∀ i, X i → AlignmentAddingPair n i → ℤ)
    (hL : ∀ i e x f, position i (L i e • x) f = position i x f + if f = e then 1 else 0)
    (hzero : ∀ i, position i (centers i) = 0)
    (schedule : List (AlignmentPlannedPivot n)) (incoming B : Finset (Fin n → ℚ))
    (hB : alignmentScheduleStates schedule incoming ⊆ B)
    (b final : Fin n → ℚ) (hb : b ∈ incoming) (hfinal : final ∈ B)
    (hreal : alignmentScheduleRealizes G X q₀ L palette requests centers schedule b final) :
    alignmentScheduleSlotsRealizes G X q₀ B L palette requests centers position schedule b final := by
  induction schedule generalizing incoming b with
  | nil => exact hreal
  | cons planned later ih =>
    obtain ⟨c, y, hreach, hreq, htail⟩ := hreal
    have hsingle : ({b} : Finset (Fin n → ℚ)) ⊆ incoming := Finset.singleton_subset_iff.mpr hb
    have hhead : alignmentAllScaleStates planned.pivot (alignmentForwardOptions planned.plan) {b} ⊆ B :=
      Finset.Subset.trans (alignmentAllScaleStates_mono _ _ _ _ hsingle)
        (Finset.Subset.trans (alignmentScheduleStates_head planned later incoming) hB)
    have hx : position planned.pivot (centers planned.pivot) ∈ ({0} : Finset _) := by
      rw [hzero]
      exact Finset.mem_singleton_self _
    have hsafe := alignmentPivotReachable_slots_safe q₀ (L planned.pivot)
      (position planned.pivot) (hL planned.pivot) planned.plan {b} B hhead {0}
      b c (centers planned.pivot) y (Finset.mem_singleton_self _) hx hreach
    have hy := alignmentPivotReachable_auxiliary_frontier q₀ (L planned.pivot)
      (position planned.pivot) (hL planned.pivot) planned.plan {b} B hhead {0}
      b c (centers planned.pivot) y (Finset.mem_singleton_self _) hx hreach
    have hc := alignmentScheduleStep_contains planned incoming b c hb
      (alignmentPivotReachable_frontier q₀ (L planned.pivot) planned.plan {b} b c
        (centers planned.pivot) y (Finset.mem_singleton_self _) hreach)
    refine ⟨c, y, ?_, hreq, ?_, ?_⟩
    · exact alignmentPivotSlotsSafe_mono q₀ (L planned.pivot) (position planned.pivot) _ _
        Finset.subset_union_left planned.plan b c (centers planned.pivot) y hsafe
    · intro request hr w hw d hd
      exact alignmentPlannedAuxiliarySlots_test requests q₀ B planned _ hy final hfinal request hr w hw d hd
    · exact ih _ (Finset.Subset.trans (alignmentScheduleStates_tail planned later incoming) hB)
        c hc htail

end Hindman168
