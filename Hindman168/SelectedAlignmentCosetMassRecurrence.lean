import Hindman168.SelectedAlignmentCosetMassPlan
namespace Hindman168
open scoped Classical
universe u

theorem selected_alignment_coset_plan_closed_cover_of_denominators {n : ℕ} {i : Fin n}
    {κ : Type} [Finite κ] (s : ℕ) (requests : List (AlignmentPivotRequest n i))
    (incoming : Finset (Fin n → ℚ))
    (q₀ : ℕ)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i (alignmentForwardOptions
        (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
        ∀ l ∈ alignmentWordLetters stage.target.words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (σ : Type) (Y : Type u) (w : σ → ℕ) (hw : ∀ j, w j ≤ s+1)
        (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
        (projection : (σ → ℝ) → Y)
        (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
          (AlignmentAddingPair n i → ℤ) → Y → ℝ)
        (θ : ℝ) (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) :
      (∀ route ∈ principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests),
        ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
        let arithmetic := alignmentJointRouteArithmetic q₀ (selectedAlignmentCosetPlan (κ := κ) s requests) b route
        let B := insert i request.tail
        let lead := a * finiteScaleBlockProduct arithmetic.1 B
        let stored := arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word
        ∀ l ∈ word, ∀ query x,
          read B lead c stored query (projection (L l.1 • x)) =
            read B lead c stored (query + alignmentAuxiliaryUnit l.1 1) (projection x)) →
      ∀ z : σ → ℝ, ∃ route ∈ principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests),
        projection ((principalPivotRouteValue q₀ L (selectedAlignmentCosetPlan (κ := κ) s requests) b route).2 • z) ∈
          alignmentJointRouteClosedSet read θ q₀ (selectedAlignmentCosetPlan (κ := κ) s requests) b requests route := by
  intro hstep z
  let plan := selectedAlignmentCosetPlan (κ := κ) s requests
  obtain ⟨b',hb',x',hx',hreach,hrequests⟩ := alignment_pivot_plan_execute (s+1) plan requests
    (selected_alignment_coset_plan_fits (κ := κ) s requests)
    (selected_alignment_coset_plan_works (κ := κ) s requests) incoming q₀ hint
    (alignmentJointShearLetter w L) (alignment_joint_shear_group_step w (s+1) hw (by omega))
    (fun B a x c => decide (3*θ/2 < read B a c x.2.toAdd 0 (projection x.1)))
    b hb hpos (z, Multiplicative.ofAdd 0)
  obtain ⟨route,hr,hscale,hpoint⟩ := principal_pivot_reachable_route q₀
    (alignmentJointShearLetter w L) plan b b' (z, Multiplicative.ofAdd 0) x' hreach
  refine ⟨route,hr,?_⟩
  apply alignment_joint_successful_route_closed w L projection read θ q₀ plan b requests route z
    (by rw [hscale,hpoint]; exact hrequests) (hstep route hr)

theorem selected_alignment_coset_plan_closed_cover {n : ℕ} {i : Fin n}
    {κ : Type} [Finite κ] (s : ℕ) (requests : List (AlignmentPivotRequest n i))
    (incoming : Finset (Fin n → ℚ))
    (σ : Type) (Y : Type u) (w : σ → ℕ) (hw : ∀ j, w j ≤ s+1)
        (L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w)
        (projection : (σ → ℝ) → Y)
        (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
          (AlignmentAddingPair n i → ℤ) → Y → ℝ)
        (θ : ℝ) (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j) :
      (∀ route ∈ principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests),
        ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
        let arithmetic := alignmentJointRouteArithmetic (selectedAlignmentCosetClearing (κ := κ) s requests incoming) (selectedAlignmentCosetPlan (κ := κ) s requests) b route
        let B := insert i request.tail
        let lead := a * finiteScaleBlockProduct arithmetic.1 B
        let stored := arithmetic.2.toAdd + alignmentAuxiliaryWord (selectedAlignmentCosetClearing (κ := κ) s requests incoming) arithmetic.1 word
        ∀ l ∈ word, ∀ query x,
          read B lead c stored query (projection (L l.1 • x)) =
            read B lead c stored (query + alignmentAuxiliaryUnit l.1 1) (projection x)) →
      ∀ z : σ → ℝ, ∃ route ∈ principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests),
        projection ((principalPivotRouteValue (selectedAlignmentCosetClearing (κ := κ) s requests incoming) L (selectedAlignmentCosetPlan (κ := κ) s requests) b route).2 • z) ∈
          alignmentJointRouteClosedSet read θ (selectedAlignmentCosetClearing (κ := κ) s requests incoming) (selectedAlignmentCosetPlan (κ := κ) s requests) b requests route := by
  exact selected_alignment_coset_plan_closed_cover_of_denominators s requests incoming
    (selectedAlignmentCosetClearing (κ := κ) s requests incoming)
    (selected_alignment_coset_clearing_denominators (κ := κ) s requests incoming)
    σ Y w hw L projection read θ b hb hpos

/-- Route count is positive before any model, coset or threshold is given. -/
theorem selected_alignment_coset_routes_nonempty {n : ℕ} {i : Fin n}
    {κ : Type} [Finite κ] (s : ℕ) (requests : List (AlignmentPivotRequest n i)) :
    (principalPivotRoutes (selectedAlignmentCosetPlan (κ := κ) s requests)).Nonempty := by
  let incoming : Finset (Fin n → ℚ) := {fun _ => 1}
  have hh := selected_alignment_coset_plan_closed_cover (κ := κ) s requests incoming
    (Fin 0) Unit (fun _ => 0) (fun _ => Nat.zero_le _) (fun _ => 1)
    (fun _ => ()) (fun _ _ _ _ _ _ => (0 : ℝ)) 0 (fun _ => 1)
    (Finset.mem_singleton_self _) (fun _ => by norm_num)
    (by intros; rfl) 0
  obtain ⟨route,hr,_⟩ := hh
  exact ⟨route,hr⟩
end Hindman168
