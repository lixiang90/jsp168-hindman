import Hindman168.AlignmentBackwardPlan

/-! The backward plan executes forward on actual scales and centers.
All visited tuples belong to the pre-enumerated scale catalogue. -/

namespace Hindman168
universe u v
open scoped Classical

def alignmentPivotReachable {n : ℕ} {i : Fin n} {G X : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (L : AlignmentAddingPair n i → G) :
    List (AlignmentPivotStage n i) → (Fin n → ℚ) → X → (Fin n → ℚ) → X → Prop
  | [], b, x, b', x' => b' = b ∧ x' = x
  | stage :: earlier, b, x, b', x' => ∃ c y p,
    alignmentPivotReachable q₀ L earlier b x c y ∧ p ∈ stage.choices ∧
      b' = alignmentScaleUpdate i stage.target.tail p.1 c ∧
      x' = alignmentWordValue q₀ c L p.2 • y

noncomputable def alignmentPivotPlanLetters {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) : Finset (AlignmentAddingPair n i × ℚ) :=
  plan.toFinset.biUnion (fun stage => alignmentWordLetters stage.target.words)

theorem alignment_pivot_plan_denominators {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) (incoming : Finset (Fin n → ℚ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ stage ∈ plan,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions plan) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨q₀, hq, hint⟩ := alignment_plan_finite_denominators i
    (alignmentForwardOptions plan) incoming (alignmentPivotPlanLetters plan)
  refine ⟨q₀, hq, ?_⟩
  intro stage hs b hb l hl
  exact hint b hb l (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hl⟩)

theorem alignment_pivot_plan_execute {n : ℕ} {i : Fin n} {Color : Type}
    {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (s : ℕ) (plan : List (AlignmentPivotStage n i))
    (requests : List (AlignmentPivotRequest n i))
    (hfit : alignmentBackwardPlanFits plan requests)
    (hworks : ∀ stage ∈ plan, AlignmentPivotStageWorks.{u, v} s Color stage)
    (incoming : Finset (Fin n → ℚ)) (q₀ : ℕ)
    (hint : ∀ stage ∈ plan,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions plan) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (L : AlignmentAddingPair n i → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (palette : Finset (Fin n) → ℚ → X → Color)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) (x : X) :
    ∃ b' ∈ alignmentScaleFrontier i (alignmentForwardOptions plan) incoming,
      ∃ x' : X, (∀ j, 0 < b' j) ∧
        alignmentPivotReachable q₀ L plan b x b' x' ∧
        ∀ request ∈ requests, alignmentPivotRequestHolds q₀ b' L palette x' request := by
  induction plan generalizing requests with
  | nil =>
    refine ⟨b, hb, x, hpos, ⟨rfl, rfl⟩, ?_⟩
    rw [hfit]
    simp only [List.not_mem_nil, false_implies, implies_true]
  | cons stage earlier ih =>
    obtain ⟨prior, rfl, hprior⟩ := hfit
    have hprefix : alignmentAllScaleStates i (alignmentForwardOptions earlier) incoming ⊆
        alignmentAllScaleStates i (alignmentForwardOptions (stage :: earlier)) incoming := by
      rw [alignmentForwardOptions_cons]
      exact alignmentAllScaleStates_contains_prefix i _ _ incoming
    have hearlier : ∀ a ∈ earlier, AlignmentPivotStageWorks.{u, v} s Color a :=
      fun a ha => hworks a (List.mem_cons_of_mem stage ha)
    have hintearlier : ∀ a ∈ earlier,
        ∀ c ∈ alignmentAllScaleStates i (alignmentForwardOptions earlier) incoming,
          ∀ l ∈ alignmentWordLetters a.target.words,
            (q₀ : ℚ) * alignmentLetterScalar c l ∈ (Int.castRingHom ℚ).range :=
      fun a ha c hc => hint a (List.mem_cons_of_mem stage ha) c (hprefix hc)
    obtain ⟨c, hc, y, hcpos, hreach, hreqs⟩ := ih _ hprior hearlier hintearlier
    have hcAll : c ∈ alignmentAllScaleStates i
        (alignmentForwardOptions (stage :: earlier)) incoming :=
      hprefix (alignmentScaleFrontier_subset_all i _ incoming hc)
    have hs := hworks stage List.mem_cons_self
    obtain ⟨p, hp, htarget⟩ := hs.2 G X q₀ c L
      (hint stage List.mem_cons_self c hcAll) hG palette y
    refine ⟨alignmentScaleUpdate i stage.target.tail p.1 c, ?_,
      alignmentWordValue q₀ c L p.2 • y,
      alignmentScaleUpdate_positive i stage.target.tail p.1 (hs.1 p hp) c hcpos,
      ⟨c, y, p, hreach, hp, rfl, rfl⟩, ?_⟩
    · rw [alignmentForwardOptions_cons, alignmentScaleFrontier_append]
      exact alignmentScaleStep_contains i (alignmentPivotStageOptions stage) _ c hc p hp
    · intro request hr
      rcases List.mem_append.mp hr with hr | hr
      · exact alignment_pivot_predecessor_preserves q₀ c L palette y stage request p hp
          (hs.1 p hp) (hreqs _ (List.mem_map.mpr ⟨request, hr, rfl⟩))
      · have hEq : request = stage.target := List.mem_singleton.mp hr
        simpa only [hEq] using htarget

end Hindman168
