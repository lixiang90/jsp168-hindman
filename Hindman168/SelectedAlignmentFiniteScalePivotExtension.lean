import Hindman168.SelectedAlignmentNativePivotExtension

/-! The original finite prediction family supplies the represented rows.
Catalogue membership discharges every scale lookup, and the final secured
predicate is the existing native finite-scale threshold predicate on the
same original full raw sample. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology ENNReal NNReal BigOperators
universe u
attribute [local instance] alignmentAddingPairFintype

theorem selected_alignment_finite_scale_pivot_extension
    {d n M r s : ℕ} {A : Finset ℚ} {Poly : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A Poly F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (requests : List (AlignmentPivotRequest n i))
    (hown : ∀ request ∈ requests, ∀ word ∈ request.words, ∀ l ∈ word,
      l.1.targetTail = request.tail)
    (incoming : Finset (Fin n → ℚ)) (q₀ : ℕ) (hq : 0 < q₀)
    (hint : ∀ stage ∈ selectedAlignmentCosetPlan (κ := Fin r) s requests,
      ∀ b ∈ alignmentAllScaleStates i
        (alignmentForwardOptions (selectedAlignmentCosetPlan (κ := Fin r) s requests)) incoming,
      ∀ l ∈ alignmentWordLetters stage.target.words,
        (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range)
    (b : Fin n → ℚ) (hb : b ∈ incoming) (hpos : ∀ j, 0 < b j)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (hS : ∀ T γ, NativePieceRepresented.{u} s F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) (S T i γ))
    (hscale : ∀ ν ∈ alignmentJointRouteFactorCatalogue (Fin r) q₀
      (selectedAlignmentCosetPlan (κ := Fin r) s requests) incoming requests, ν.2.1 ∈ A)
    (θ : ℝ) (hθ : 0 < θ) :
    let plan := selectedAlignmentCosetPlan (κ := Fin r) s requests
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop,
      ∀ E : (Fin M → ℕ) → Prop,
      (∀ x y, (∀ j < principalAlignmentEmbedding e heM i, x j = y j) → (E x ↔ E y)) →
      (1 / (3 * ((principalPivotRoutes plan).card : ℝ)^2)) *
        event (globalRawMass (F.cutoff w) (primorial w) M) E - err w ≤
      event (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => E x ∧ ∃ route ∈ principalPivotRoutes plan, ∀ request ∈ requests,
          principalThresholdRequestHolds q₀ (alignmentJointRouteArithmetic q₀ plan b route).1
            (principalNativeLetter (principalAlignmentEmbedding e heM))
            (principalNativeScaleObservation e heM F A S q₀ w x i) θ 1 request) := by
  let SS : Finset (Fin n) → ℚ → Fin r → ℕ → ℤ → ℝ :=
    fun T a c w z => if ha : a ∈ A then S T i (⟨a,ha⟩,c) w z else 0
  have hrep : ∀ ν : alignmentJointRouteFactorCatalogue (Fin r) q₀
      (selectedAlignmentCosetPlan (κ := Fin r) s requests) incoming requests,
      NativePieceRepresented.{u} s F (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M))
        (SS (ν.val.1.erase i) ν.val.2.1 ν.val.2.2.1) := by
    intro ν
    simpa only [SS, dif_pos (hscale ν.val ν.property)] using
      hS (ν.val.1.erase i) (⟨ν.val.2.1,hscale ν.val ν.property⟩,ν.val.2.2.1)
  obtain ⟨err,he,hh⟩ := selected_alignment_native_pivot_extension hF e heM i requests hown
    incoming q₀ hq hint b hb hpos SS θ hθ hrep
  refine ⟨err,he,?_⟩
  filter_upwards [hh] with w hw E hE
  have h := hw E hE
  have hindex : principalAlignmentEmbedding e heM i = selectedPrincipalIndex e heM i := rfl
  simpa only [selectedAlignmentSignedRouteSecured, SS, hindex,
    selected_alignment_signed_observation_eq_native_scale] using h

end Hindman168
