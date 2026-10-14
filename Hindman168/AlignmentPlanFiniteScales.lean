import Hindman168.AlignmentScalePaths
import Hindman168.AlignmentFiniteDenominators

/-! The finite path catalogue supplies a common denominator and positive
palette scale list, including every subset product of a terminal tuple. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentPlanPaletteIndices {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ) : Finset ℚ :=
  (alignmentAllScaleStates i stages incoming).biUnion
    (fun b => blocks.biUnion (fun B => leading.image (fun a => a * finiteScaleBlockProduct b B)))

noncomputable def alignmentPlanPredictionScales {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ) : Finset ℚ :=
  finiteScaleProductClosure (alignmentScaleFrontier i stages incoming)
    (alignmentPlanPaletteIndices i stages incoming blocks leading)

theorem alignmentPlanPaletteIndices_contains {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ)
    (b : Fin n → ℚ) (hb : b ∈ alignmentAllScaleStates i stages incoming)
    (B : Finset (Fin n)) (hB : B ∈ blocks) (a : ℚ) (ha : a ∈ leading) :
    a * finiteScaleBlockProduct b B ∈ alignmentPlanPaletteIndices i stages incoming blocks leading :=
  Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr
    ⟨B, hB, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩⟩

theorem alignmentPlanPaletteIndices_positive {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ)
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hstages : ∀ stage ∈ stages, ∀ p ∈ stage.2, 0 < p.1)
    (hleading : ∀ a ∈ leading, 0 < a) :
    ∀ a ∈ alignmentPlanPaletteIndices i stages incoming blocks leading, 0 < a := by
  intro a ha
  obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨B, _, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  exact mul_pos (hleading c hc) (finiteScaleBlockProduct_positive b
    (alignmentAllScaleStates_positive i stages incoming hin hstages b hb) B)

theorem alignmentPlanPredictionScales_positive {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ)
    (hin : ∀ b ∈ incoming, ∀ j, 0 < b j)
    (hstages : ∀ stage ∈ stages, ∀ p ∈ stage.2, 0 < p.1)
    (hleading : ∀ a ∈ leading, 0 < a) :
    ∀ a ∈ alignmentPlanPredictionScales i stages incoming blocks leading, 0 < a :=
  finiteScaleProductClosure_positive _ _
    (alignmentScaleFrontier_positive i stages incoming hin hstages)
    (alignmentPlanPaletteIndices_positive i stages incoming blocks leading hin hstages hleading)

theorem alignmentPlanPredictionScales_contains_palette {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ) :
    alignmentPlanPaletteIndices i stages incoming blocks leading ⊆
      alignmentPlanPredictionScales i stages incoming blocks leading :=
  finiteScaleProductClosure_contains _ _

theorem alignmentPlanPredictionScales_closed {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (blocks : Finset (Finset (Fin n))) (leading : Finset ℚ) :
    FiniteScaleClosure (alignmentScaleFrontier i stages incoming)
      (alignmentPlanPredictionScales i stages incoming blocks leading) :=
  finiteScaleProductClosure_closed _ _

theorem alignment_plan_finite_denominators {n : ℕ} (i : Fin n)
    (stages : List (AlignmentStageOptions n i)) (incoming : Finset (Fin n → ℚ))
    (letters : Finset (AlignmentAddingPair n i × ℚ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ b ∈ alignmentAllScaleStates i stages incoming,
      ∀ l ∈ letters, (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range :=
  alignment_finite_letter_denominators (alignmentAllScaleStates i stages incoming) letters

end Hindman168
