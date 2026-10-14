import Hindman168.SelectedAlignmentNativeRouteFailure
import Hindman168.SelectedAlignmentRouteRawExtension

/-! The actual native pivot extension, uniform in every earlier raw event.
Only original representation and fixed finite-plan arithmetic enter; local
laws, likelihood, fine conditioning and signed shift removal are proved. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology ENNReal NNReal BigOperators
universe u
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_native_pivot_extension
    {d n M s : ℕ} {κ : Type} [Fintype κ]
    {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (requests : List (AlignmentPivotRequest n i))
    (hown : ∀ request ∈ requests, ∀ word ∈ request.words, ∀ l ∈ word,
      l.1.targetTail = request.tail)
    (incoming : Finset (Fin n → ℚ)) (q₀ : ℕ) (hq : 0 < q₀)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := κ) s requests,
      ∀ b ∈ alignmentAllScaleStates i
        (alignmentForwardOptions (selectedAlignmentCosetPlan (κ := κ) s requests)) incoming,
      ∀ l ∈ alignmentWordLetters stage.target.words,
        (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j)
    (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (θ : ℝ) (hθ : 0 < θ) :
    let plan := selectedAlignmentCosetPlan (κ := κ) s requests
    let catalogue := alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests
    (∀ ν : catalogue, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
      (S (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1)) →
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      ∀ E : (Fin M → ℕ) → Prop,
      (∀ x y, (∀ j < principalAlignmentEmbedding e heM i, x j = y j) → (E x ↔ E y)) →
      (1 / (3 * ((principalPivotRoutes plan).card : ℝ)^2)) *
        event (globalRawMass (F.cutoff w) (primorial w) M) E - err w ≤
      event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => E x ∧ selectedAlignmentSignedRouteSecured (principalAlignmentEmbedding e heM) i F q₀ w
          x S θ plan b requests (x (principalAlignmentEmbedding e heM i))) := by
  dsimp only
  intro hrep
  apply selected_alignment_route_full_raw_extension hF e heM i q₀ hq S θ _ incoming b hb requests
    (Finset.card_pos.mpr (selected_alignment_coset_routes_nonempty (κ := κ) s requests))
  exact selected_alignment_native_route_failure_tendsto hF e heM i requests hown incoming q₀ hq
    hint b hb hpos S θ hθ hrep

end Hindman168
