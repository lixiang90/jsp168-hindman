import Hindman168.SelectedAlignmentRecipeRouteFailure
import Hindman168.SelectedAlignmentRecipeArrayModels

/-! The actual represented functions alone suffice for vanishing local route
failure mass. All native models, recipes, finite evaluations and bases are
constructed before extraction; no compactness or Haar hypothesis remains. -/
namespace Hindman168
open Filter MeasureTheory FiniteMass Module
open scoped Topology Manifold ContDiff Classical ENNReal NNReal
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

theorem selected_alignment_native_route_failure_tendsto
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
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => selectedAlignmentRawRouteCellMass F e heM i q₀ w x S θ plan b requests <
        ((3 / (4 * ((principalPivotRoutes plan).card : ℝ≥0)) : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 0) := by
  dsimp only
  intro hrep
  obtain ⟨D,r,v,hv,dim,basis,obs,g,a,B,Lip,_,hB,hLip,hrecipe⟩ :=
    selected_alignment_recipe_array_models (principalAlignmentEmbedding e heM i) F
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) _ hrep
  exact selected_alignment_recipe_route_failure_tendsto hF e heM i requests hown incoming q₀ hq
    hint b hb hpos S θ hθ D r v hv dim basis obs g a B Lip hB hLip hrecipe

end Hindman168
