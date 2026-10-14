import Hindman168.AlignmentWordInflation

/-! The predecessor budgets are unions over every alternative, so a
single old requirement protects all possible next updates and jumps. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentChoicePredecessorLeading {n : ℕ} {i : Fin n}
    (T B : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (leading : Finset ℚ) : Finset ℚ :=
  choices.biUnion (fun p => alignmentPredecessorLeading i T B p.1 leading)

noncomputable def alignmentChoicePredecessorWords {n : ℕ} {i : Fin n}
    (T : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    Finset (List (AlignmentAddingPair n i × ℚ)) :=
  choices.biUnion (fun p => alignmentPredecessorWords T p.1 p.2 words)

theorem alignmentPaletteRequirement_mono {n : ℕ} {i : Fin n}
    {G X Color : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (B : Finset (Fin n)) (palette : ℚ → X → Color) (x : X)
    (leading oldLeading : Finset ℚ)
    (words oldWords : Finset (List (AlignmentAddingPair n i × ℚ)))
    (hLeading : leading ⊆ oldLeading) (hWords : words ⊆ oldWords)
    (hreq : alignmentPaletteRequirement q₀ b L B palette oldLeading oldWords x) :
    alignmentPaletteRequirement q₀ b L B palette leading words x :=
  fun a ha w hw => hreq a (hLeading ha) w (hWords hw)

theorem alignmentChoicePredecessorLeading_subset {n : ℕ} {i : Fin n}
    (T B : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (leading : Finset ℚ) (p : ℕ × List (AlignmentAddingPair n i × ℚ))
    (hp : p ∈ choices) :
    alignmentPredecessorLeading i T B p.1 leading ⊆
      alignmentChoicePredecessorLeading T B choices leading :=
  fun _ ha => Finset.mem_biUnion.mpr ⟨p, hp, ha⟩

theorem alignmentChoicePredecessorWords_subset {n : ℕ} {i : Fin n}
    (T : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (words : Finset (List (AlignmentAddingPair n i × ℚ)))
    (p : ℕ × List (AlignmentAddingPair n i × ℚ)) (hp : p ∈ choices) :
    alignmentPredecessorWords T p.1 p.2 words ⊆
      alignmentChoicePredecessorWords T choices words :=
  fun _ hw => Finset.mem_biUnion.mpr ⟨p, hp, hw⟩

theorem alignment_all_choices_predecessor_preserves {n : ℕ} {i : Fin n}
    {G X Color : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (T B : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (leading : Finset ℚ) (words : Finset (List (AlignmentAddingPair n i × ℚ)))
    (palette : ℚ → X → Color) (x : X)
    (hreq : alignmentPaletteRequirement q₀ b L B palette
      (alignmentChoicePredecessorLeading T B choices leading)
      (alignmentChoicePredecessorWords T choices words) x)
    (p : ℕ × List (AlignmentAddingPair n i × ℚ)) (hp : p ∈ choices) (hk : 0 < p.1) :
    alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T p.1 b) L B palette leading words
      (alignmentWordValue q₀ b L p.2 • x) := by
  apply alignment_predecessor_preserves q₀ b L T B p.1 hk palette leading words p.2 x
  exact alignmentPaletteRequirement_mono q₀ b L B palette x _ _ _ _
    (alignmentChoicePredecessorLeading_subset T B choices leading p hp)
    (alignmentChoicePredecessorWords_subset T choices words p hp) hreq

theorem alignmentChoicePredecessorLeading_positive {n : ℕ} {i : Fin n}
    (T B : Finset (Fin n))
    (choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (leading : Finset ℚ) (hpos : ∀ p ∈ choices, 0 < p.1)
    (hleading : ∀ a ∈ leading, 0 < a) :
    ∀ a ∈ alignmentChoicePredecessorLeading T B choices leading, 0 < a := by
  intro a ha
  obtain ⟨p, hp, himage⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp himage
  exact mul_pos (hleading c hc) (finiteScaleBlockProduct_positive _
    (alignmentMultiplier_positive i T p.1 (hpos p hp)) B)

end Hindman168
