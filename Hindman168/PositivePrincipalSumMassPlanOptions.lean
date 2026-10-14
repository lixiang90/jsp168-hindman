import Hindman168.AlignmentUniformPivotPlan
import Hindman168.AlignmentNilpotentRecurrence

/-! The fixed finite route catalogue of an actual pivot plan. A route
records only finite stage choices, before any group, model, or threshold.
Its interpreted word is a single fixed group element for that route. -/
namespace Hindman168
open scoped BigOperators Classical
universe u v

noncomputable def principalPivotRoutes {n : ℕ} {i : Fin n} :
    List (AlignmentPivotStage n i) → Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))
  | [] => {[]}
  | stage :: earlier => ((principalPivotRoutes earlier).product stage.choices).image
      (fun p => p.2 :: p.1)

noncomputable def principalPivotRouteValue {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (L : AlignmentAddingPair n i → G) :
    List (AlignmentPivotStage n i) → (Fin n → ℚ) →
      List (ℕ × List (AlignmentAddingPair n i × ℚ)) → (Fin n → ℚ) × G
  | [], b, _ => (b, 1)
  | _ :: _, b, [] => (b, 1)
  | stage :: earlier, b, p :: route =>
      let previous := principalPivotRouteValue q₀ L earlier b route
      (alignmentScaleUpdate i stage.target.tail p.1 previous.1,
        alignmentWordValue q₀ previous.1 L p.2 * previous.2)

theorem principal_pivot_routes_card {n : ℕ} {i : Fin n}
    (plan : List (AlignmentPivotStage n i)) :
    (principalPivotRoutes plan).card = (plan.map (fun stage => stage.choices.card)).prod := by
  induction plan with
  | nil => simp [principalPivotRoutes]
  | cons stage earlier ih =>
    have hinj : Function.Injective
        (fun p : List (ℕ × List (AlignmentAddingPair n i × ℚ)) ×
          (ℕ × List (AlignmentAddingPair n i × ℚ)) => p.2 :: p.1) := by
      intro p q h
      have hh := List.cons.inj h
      exact Prod.ext hh.2 hh.1
    rw [principalPivotRoutes, Finset.card_image_of_injective _ hinj, Finset.product_eq_sprod, Finset.card_product, ih]
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_comm _ _

theorem principal_pivot_reachable_route {n : ℕ} {i : Fin n} {G X : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (L : AlignmentAddingPair n i → G)
    (plan : List (AlignmentPivotStage n i)) (b b' : Fin n → ℚ) (x x' : X)
    (hr : alignmentPivotReachable q₀ L plan b x b' x') :
    ∃ route ∈ principalPivotRoutes plan,
      (principalPivotRouteValue q₀ L plan b route).1 = b' ∧
      (principalPivotRouteValue q₀ L plan b route).2 • x = x' := by
  induction plan generalizing b' x' with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨[], Finset.mem_singleton_self _, rfl, one_smul _ _⟩
  | cons stage earlier ih =>
    obtain ⟨c, y, p, hreach, hp, rfl, rfl⟩ := hr
    obtain ⟨route, hroute, hscale, hpoint⟩ := ih c y hreach
    refine ⟨p :: route, Finset.mem_image.mpr
      ⟨(route,p), Finset.mem_product.mpr ⟨hroute,hp⟩, rfl⟩, ?_, ?_⟩
    · simp only [principalPivotRouteValue, hscale]
    · simp only [principalPivotRouteValue, hscale, mul_smul, hpoint]

/-- The existing proved nilpotent recurrence produces a finite route plan.
In particular its route count precedes all later groups/actions/palettes. -/
theorem principal_recurrence_finite_routes {n : ℕ} {i : Fin n} {Color : Type}
    [Finite Color] (s : ℕ) (requests : List (AlignmentPivotRequest n i)) :
    ∃ plan : List (AlignmentPivotStage n i),
      ∀ incoming : Finset (Fin n → ℚ), ∃ q₀ : ℕ, 0 < q₀ ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (L : AlignmentAddingPair n i → G)
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (palette : Finset (Fin n) → ℚ → X → Color)
        (b : Fin n → ℚ) (_hb : b ∈ incoming) (_hpos : ∀ j, 0 < b j) (x : X),
        ∃ route ∈ principalPivotRoutes plan, ∀ request ∈ requests,
          alignmentPivotRequestHolds q₀ (principalPivotRouteValue q₀ L plan b route).1 L palette
            ((principalPivotRouteValue q₀ L plan b route).2 • x) request := by
  obtain ⟨plan, _, _, hplan⟩ := alignment_uniform_pivot_plan.{u,v} (Color := Color)
    s (hasAlignmentMonomialRecurrence s) requests
  refine ⟨plan, ?_⟩
  intro incoming
  obtain ⟨q₀, hq, hqplan⟩ := hplan incoming
  refine ⟨q₀, hq, ?_⟩
  intro G _ X _ L hG palette b hb hpos x
  obtain ⟨b', _, x', _, hr, hrequests⟩ := hqplan G X L hG palette b hb hpos x
  obtain ⟨route, hroute, hscale, hpoint⟩ := principal_pivot_reachable_route q₀ L plan b b' x x' hr
  refine ⟨route, hroute, ?_⟩
  simpa only [hscale, hpoint] using hrequests

end Hindman168
