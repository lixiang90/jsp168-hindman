import Hindman168.AlignmentMonomialRecurrenceInput
import Hindman168.AlignmentChoicePredecessors

/-! One forward stage establishes its own target and preserves every
previous target whose backward budget covered all possible choices. -/

namespace Hindman168
universe u v
open scoped Classical

theorem alignment_stage_advance {n : ℕ} {i : Fin n} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (leading : Finset ℚ) (words : Finset (List (AlignmentAddingPair n i × ℚ)))
    (previous : Finset (Finset (Fin n))) (oldLeading : Finset (Fin n) → Finset ℚ)
    (oldWords : Finset (Fin n) → Finset (List (AlignmentAddingPair n i × ℚ))) :
    ∃ choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)),
      (∀ p ∈ choices, 0 < p.1) ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (q₀ : ℕ) (b : Fin n → ℚ) (_hb : ∀ j, 0 < b j)
        (L : AlignmentAddingPair n i → G),
        (∀ l ∈ alignmentWordLetters words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range) →
        ∀ (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
          (palette : Finset (Fin n) → ℚ → X → Color) (x : X),
          (∀ B ∈ previous, alignmentPaletteRequirement q₀ b L B (palette B)
            (alignmentChoicePredecessorLeading T B choices (oldLeading B))
            (alignmentChoicePredecessorWords T choices (oldWords B)) x) →
          ∃ p ∈ choices,
            (∀ j, 0 < alignmentScaleUpdate i T p.1 b j) ∧
            alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T p.1 b) L
              (insert i T) (palette (insert i T)) leading words
              (alignmentWordValue q₀ b L p.2 • x) ∧
            ∀ B ∈ previous, alignmentPaletteRequirement q₀
              (alignmentScaleUpdate i T p.1 b) L B (palette B)
              (oldLeading B) (oldWords B) (alignmentWordValue q₀ b L p.2 • x) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_actual_target_choices.{u, v}
    (Color := Color) s hrec T hT leading words
  refine ⟨Ω, hpos, ?_⟩
  intro G _ X _ q₀ b hb L hint hG palette x hprior
  obtain ⟨p, hp, htarget⟩ := hΩ G X q₀ b L hint hG (palette (insert i T)) x
  refine ⟨p, hp, alignmentScaleUpdate_positive i T p.1 (hpos p hp) b hb, htarget, ?_⟩
  intro B hB
  exact alignment_all_choices_predecessor_preserves q₀ b L T B Ω (oldLeading B)
    (oldWords B) (palette B) x (hprior B hB) p hp (hpos p hp)

end Hindman168
