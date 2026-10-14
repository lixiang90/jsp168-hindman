import Hindman168.AlignmentFutureRequests
import Hindman168.AlignmentMultiplierCatalog

/-! A fixed-pivot plan protects every requested comparison through every
prescribed later multiplier while retaining its actual endpoint center. -/

namespace Hindman168
universe u v

theorem alignment_future_pivot_plan {n : ℕ} {i : Fin n} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (requests : List (AlignmentPivotRequest n i)) (futures : Finset (Fin n → ℚ))
    (hfutures : ∀ d ∈ futures, ∀ j, 0 < d j) :
    ∃ plan : List (AlignmentPivotStage n i),
      alignmentBackwardPlanFits plan (requests.map (alignmentFutureRequest futures)) ∧
      (∀ stage ∈ plan, ∀ p ∈ stage.choices, 0 < p.1) ∧
      (∀ stage ∈ plan, AlignmentPivotStageWorks.{u, v} s Color stage) ∧
      ∀ incoming : Finset (Fin n → ℚ), ∃ q₀ : ℕ, 0 < q₀ ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (L : AlignmentAddingPair n i → G)
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (palette : Finset (Fin n) → ℚ → X → Color)
        (b : Fin n → ℚ) (_hb : b ∈ incoming) (_hpos : ∀ j, 0 < b j) (x : X),
        ∃ b' ∈ alignmentScaleFrontier i (alignmentForwardOptions plan) incoming,
          ∃ x' : X, alignmentPivotReachable q₀ L plan b x b' x' ∧
            (∀ j, 0 < b' j) ∧ ∀ d ∈ futures,
              (∀ j, 0 < alignmentMultiplyScales b' d j) ∧
              ∀ request ∈ requests,
                alignmentPivotRequestHolds q₀ (alignmentMultiplyScales b' d) L palette x' request := by
  obtain ⟨plan, hfit, hworks⟩ := alignment_backward_plan_exists.{u, v}
    (Color := Color) s hrec (requests.map (alignmentFutureRequest futures))
  refine ⟨plan, hfit, fun stage hs => (hworks stage hs).1, hworks, ?_⟩
  intro incoming
  obtain ⟨q₀, hq, hint⟩ := alignment_pivot_plan_denominators plan incoming
  refine ⟨q₀, hq, ?_⟩
  intro G _ X _ L hG palette b hb hpos x
  obtain ⟨b', hb', x', hbpos, hreach, hrequests⟩ := alignment_pivot_plan_execute
    s plan _ hfit hworks incoming q₀ hint L hG palette b hb hpos x
  refine ⟨b', hb', x', hreach, hbpos, ?_⟩
  intro d hd
  refine ⟨alignmentMultiplyScales_positive b' d hbpos (hfutures d hd), ?_⟩
  intro request hr
  exact alignmentFutureRequest_transport q₀ b' d L palette x' futures hd request
    (hrequests _ (List.mem_map.mpr ⟨request, hr, rfl⟩))

end Hindman168
