import Hindman168.AlignmentPivotExecution

/-! A complete finite plan at one pivot, conditional on genuine monomial
recurrence. Plan and common denominator precede every group, action and palette. -/

namespace Hindman168
universe u v

theorem alignment_uniform_pivot_plan {n : ℕ} {i : Fin n} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (requests : List (AlignmentPivotRequest n i)) :
    ∃ plan : List (AlignmentPivotStage n i), alignmentBackwardPlanFits plan requests ∧
      (∀ stage ∈ plan, ∀ p ∈ stage.choices, 0 < p.1) ∧
      ∀ incoming : Finset (Fin n → ℚ), ∃ q₀ : ℕ, 0 < q₀ ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (L : AlignmentAddingPair n i → G)
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (palette : Finset (Fin n) → ℚ → X → Color)
        (b : Fin n → ℚ) (_hb : b ∈ incoming) (_hpos : ∀ j, 0 < b j) (x : X),
        ∃ b' ∈ alignmentScaleFrontier i (alignmentForwardOptions plan) incoming,
          ∃ x' : X, (∀ j, 0 < b' j) ∧
            alignmentPivotReachable q₀ L plan b x b' x' ∧
            ∀ request ∈ requests, alignmentPivotRequestHolds q₀ b' L palette x' request := by
  obtain ⟨plan, hfit, hworks⟩ := alignment_backward_plan_exists.{u, v}
    (Color := Color) s hrec requests
  refine ⟨plan, hfit, fun stage hs => (hworks stage hs).1, ?_⟩
  intro incoming
  obtain ⟨q₀, hq, hint⟩ := alignment_pivot_plan_denominators plan incoming
  refine ⟨q₀, hq, ?_⟩
  intro G _ X _ L hG palette b hb hpos x
  exact alignment_pivot_plan_execute s plan requests hfit hworks incoming q₀ hint
    L hG palette b hb hpos x

end Hindman168
