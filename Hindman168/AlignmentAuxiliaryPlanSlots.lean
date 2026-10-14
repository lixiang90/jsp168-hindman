import Hindman168.AlignmentAuxiliaryWords

/-! Finite auxiliary frontiers follow the actual forward order of the
backward-stored plan. Visits include every unit-power intermediate slot. -/

namespace Hindman168
open scoped Classical

def alignmentPivotSlotsSafe {n : ℕ} {i : Fin n} {G X : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ) (slots : Finset (AlignmentAddingPair n i → ℤ)) :
    List (AlignmentPivotStage n i) → (Fin n → ℚ) → X → (Fin n → ℚ) → X → Prop
  | [], b, x, b', x' => b' = b ∧ x' = x ∧ position x ∈ slots
  | stage :: earlier, b, x, b', x' => ∃ c y p,
    alignmentPivotSlotsSafe q₀ L position slots earlier b x c y ∧ p ∈ stage.choices ∧
      b' = alignmentScaleUpdate i stage.target.tail p.1 c ∧
      x' = alignmentWordValue q₀ c L p.2 • y ∧
      ∀ d ∈ alignmentAuxiliaryWordVisits q₀ c p.2, position y + d ∈ slots

noncomputable def alignmentAuxiliaryFrontier {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) :
    List (AlignmentPivotStage n i) → Finset (AlignmentAddingPair n i → ℤ) →
      Finset (AlignmentAddingPair n i → ℤ)
  | [], initial => initial
  | stage :: earlier, initial =>
    (alignmentAuxiliaryFrontier q₀ B earlier initial).biUnion (fun v => B.biUnion (fun b =>
      stage.choices.image (fun p => v + alignmentAuxiliaryWord q₀ b p.2)))

noncomputable def alignmentAuxiliaryPlanVisits {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) :
    List (AlignmentPivotStage n i) → Finset (AlignmentAddingPair n i → ℤ) →
      Finset (AlignmentAddingPair n i → ℤ)
  | [], initial => initial
  | stage :: earlier, initial =>
    alignmentAuxiliaryPlanVisits q₀ B earlier initial ∪
      (alignmentAuxiliaryFrontier q₀ B earlier initial).biUnion (fun v => B.biUnion (fun b =>
        stage.choices.biUnion (fun p => (alignmentAuxiliaryWordVisits q₀ b p.2).image (v + ·))))

theorem alignmentAuxiliaryFrontier_contains {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) (stage : AlignmentPivotStage n i)
    (earlier : List (AlignmentPivotStage n i)) (initial : Finset (AlignmentAddingPair n i → ℤ))
    (v : AlignmentAddingPair n i → ℤ) (hv : v ∈ alignmentAuxiliaryFrontier q₀ B earlier initial)
    (b : Fin n → ℚ) (hb : b ∈ B) (p : ℕ × List (AlignmentAddingPair n i × ℚ))
    (hp : p ∈ stage.choices) :
    v + alignmentAuxiliaryWord q₀ b p.2 ∈ alignmentAuxiliaryFrontier q₀ B (stage :: earlier) initial :=
  Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_biUnion.mpr ⟨b, hb,
    Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩⟩

theorem alignmentAuxiliaryPlanVisits_contains_initial {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) (plan : List (AlignmentPivotStage n i))
    (initial : Finset (AlignmentAddingPair n i → ℤ)) :
    initial ⊆ alignmentAuxiliaryPlanVisits q₀ B plan initial := by
  induction plan with
  | nil => exact Finset.Subset.refl initial
  | cons stage earlier ih => exact Finset.Subset.trans ih Finset.subset_union_left

theorem alignmentAuxiliaryPlanVisits_contains_frontier {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) (plan : List (AlignmentPivotStage n i))
    (initial : Finset (AlignmentAddingPair n i → ℤ)) :
    alignmentAuxiliaryFrontier q₀ B plan initial ⊆ alignmentAuxiliaryPlanVisits q₀ B plan initial := by
  cases plan with
  | nil => exact Finset.Subset.refl initial
  | cons stage earlier =>
    intro v hv
    obtain ⟨a, ha, hbUnion⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨b, hb, hpImage⟩ := Finset.mem_biUnion.mp hbUnion
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpImage
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨p, hp,
        Finset.mem_image.mpr ⟨_, alignmentAuxiliaryWordVisits_endpoint q₀ b p.2, rfl⟩⟩⟩⟩)

theorem alignmentAuxiliaryPlanVisits_word {n : ℕ} {i : Fin n}
    (q₀ : ℕ) (B : Finset (Fin n → ℚ)) (stage : AlignmentPivotStage n i)
    (earlier : List (AlignmentPivotStage n i)) (initial : Finset (AlignmentAddingPair n i → ℤ))
    (v : AlignmentAddingPair n i → ℤ) (hv : v ∈ alignmentAuxiliaryFrontier q₀ B earlier initial)
    (b : Fin n → ℚ) (hb : b ∈ B) (p : ℕ × List (AlignmentAddingPair n i × ℚ))
    (hp : p ∈ stage.choices) (d : AlignmentAddingPair n i → ℤ)
    (hd : d ∈ alignmentAuxiliaryWordVisits q₀ b p.2) :
    v + d ∈ alignmentAuxiliaryPlanVisits q₀ B (stage :: earlier) initial :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv,
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩⟩⟩)

theorem alignmentPivotReachable_frontier {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (b b' : Fin n → ℚ) (x x' : X)
    (hb : b ∈ incoming) (hreach : alignmentPivotReachable q₀ L plan b x b' x') :
    b' ∈ alignmentScaleFrontier i (alignmentForwardOptions plan) incoming := by
  induction plan generalizing b' x' with
  | nil => exact hreach.1.symm ▸ hb
  | cons stage earlier ih =>
    obtain ⟨c, y, p, hr, hp, rfl, rfl⟩ := hreach
    rw [alignmentForwardOptions_cons, alignmentScaleFrontier_append]
    exact alignmentScaleStep_contains i (alignmentPivotStageOptions stage) _ c (ih c y hr) p hp

theorem alignmentPivotReachable_auxiliary_frontier {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (plan : List (AlignmentPivotStage n i)) (incoming B : Finset (Fin n → ℚ))
    (hB : alignmentAllScaleStates i (alignmentForwardOptions plan) incoming ⊆ B)
    (initial : Finset (AlignmentAddingPair n i → ℤ))
    (b b' : Fin n → ℚ) (x x' : X) (hb : b ∈ incoming) (hx : position x ∈ initial)
    (hreach : alignmentPivotReachable q₀ L plan b x b' x') :
    position x' ∈ alignmentAuxiliaryFrontier q₀ B plan initial := by
  induction plan generalizing b' x' with
  | nil => exact hreach.2.symm ▸ hx
  | cons stage earlier ih =>
    obtain ⟨c, y, p, hr, hp, rfl, rfl⟩ := hreach
    have hprefix : alignmentAllScaleStates i (alignmentForwardOptions earlier) incoming ⊆
        alignmentAllScaleStates i (alignmentForwardOptions (stage :: earlier)) incoming := by
      rw [alignmentForwardOptions_cons]
      exact alignmentAllScaleStates_contains_prefix i _ _ incoming
    have hc : c ∈ B := hB (hprefix (alignmentScaleFrontier_subset_all i _ incoming
      (alignmentPivotReachable_frontier q₀ L earlier incoming b c x y hb hr)))
    have hy := ih (Finset.Subset.trans hprefix hB) c y hr
    rw [alignmentWordValue_auxiliary_translation q₀ c L position hL p.2 y]
    exact alignmentAuxiliaryFrontier_contains q₀ B stage earlier initial _ hy c hc p hp

theorem alignmentPivotSlotsSafe_mono {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G) (position : X → AlignmentAddingPair n i → ℤ)
    (first second : Finset (AlignmentAddingPair n i → ℤ)) (hs : first ⊆ second)
    (plan : List (AlignmentPivotStage n i)) (b b' : Fin n → ℚ) (x x' : X)
    (hsafe : alignmentPivotSlotsSafe q₀ L position first plan b x b' x') :
    alignmentPivotSlotsSafe q₀ L position second plan b x b' x' := by
  induction plan generalizing b' x' with
  | nil => exact ⟨hsafe.1, hsafe.2.1, hs hsafe.2.2⟩
  | cons stage earlier ih =>
    obtain ⟨c, y, p, hprior, hp, rfl, rfl, hwords⟩ := hsafe
    exact ⟨c, y, p, ih c y hprior, hp, rfl, rfl, fun d hd => hs (hwords d hd)⟩

theorem alignmentPivotReachable_slots_safe {n : ℕ} {i : Fin n}
    {G X : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G)
    (position : X → AlignmentAddingPair n i → ℤ)
    (hL : ∀ e x f, position (L e • x) f = position x f + if f = e then 1 else 0)
    (plan : List (AlignmentPivotStage n i)) (incoming B : Finset (Fin n → ℚ))
    (hB : alignmentAllScaleStates i (alignmentForwardOptions plan) incoming ⊆ B)
    (initial : Finset (AlignmentAddingPair n i → ℤ))
    (b b' : Fin n → ℚ) (x x' : X) (hb : b ∈ incoming) (hx : position x ∈ initial)
    (hreach : alignmentPivotReachable q₀ L plan b x b' x') :
    alignmentPivotSlotsSafe q₀ L position (alignmentAuxiliaryPlanVisits q₀ B plan initial)
      plan b x b' x' := by
  induction plan generalizing b' x' with
  | nil => exact ⟨hreach.1, hreach.2, hx⟩
  | cons stage earlier ih =>
    obtain ⟨c, y, p, hr, hp, rfl, rfl⟩ := hreach
    have hprefix : alignmentAllScaleStates i (alignmentForwardOptions earlier) incoming ⊆
        alignmentAllScaleStates i (alignmentForwardOptions (stage :: earlier)) incoming := by
      rw [alignmentForwardOptions_cons]
      exact alignmentAllScaleStates_contains_prefix i _ _ incoming
    have hbprior := Finset.Subset.trans hprefix hB
    have hc : c ∈ B := hbprior (alignmentScaleFrontier_subset_all i _ incoming
      (alignmentPivotReachable_frontier q₀ L earlier incoming b c x y hb hr))
    have hy := alignmentPivotReachable_auxiliary_frontier q₀ L position hL earlier incoming B
      hbprior initial b c x y hb hx hr
    refine ⟨c, y, p, ?_, hp, rfl, rfl, ?_⟩
    · exact alignmentPivotSlotsSafe_mono q₀ L position _ _ Finset.subset_union_left earlier b c x y
        (ih hbprior c y hr)
    · intro d hd
      exact alignmentAuxiliaryPlanVisits_word q₀ B stage earlier initial _ hy c hc p hp d hd

end Hindman168
