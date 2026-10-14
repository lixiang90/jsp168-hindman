import Hindman168.AlignmentFiniteWordAlphabet

/-! The still unproved recurrence input is stated explicitly on finite
alphabets and finite palettes. Its finite target consequence is proved,
using the earlier free-group compactness and signed-word interpretation. -/

namespace Hindman168
universe u v
open scoped Classical

def HasAlignmentMonomialRecurrence (s : ℕ) : Prop :=
  ∀ (E Color : Type) [Finite E] [Finite Color] (degree : E → ℕ),
    (∀ e, 0 < degree e) → ∀ (words : Finset (List E))
      (χ : AlignmentFreeNilpotent E s → Color), ∃ k J,
        0 < k ∧ ∀ w ∈ words, χ J =
          χ (alignmentMonomialWord (alignmentFreeGenerator s) degree w k * J)

theorem alignment_actual_target_choices {n : ℕ} {i : Fin n} {Color : Type}
    [Finite Color] (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (leading : Finset ℚ) (words : Finset (List (AlignmentAddingPair n i × ℚ))) :
    ∃ choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ)),
      (∀ p ∈ choices, 0 < p.1) ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G),
        (∀ l ∈ alignmentWordLetters words,
          (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range) →
        ∀ (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
          (palette : ℚ → X → Color) (x : X), ∃ p ∈ choices,
          alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T p.1 b) L
            (insert i T) palette leading words (alignmentWordValue q₀ b L p.2 • x) := by
  let E := {l // l ∈ alignmentWordLetters words}
  let degree : E → ℕ := fun e => (alignmentPairInflationExponent e.val.1 T).toNat
  have hdegree : ∀ e, 0 < degree e := by
    intro e
    change 0 < (alignmentPairInflationExponent e.val.1 T).toNat
    have h := alignmentPairInflationExponent_positive e.val.1 T
    omega
  have hr := hrec E ({a : ℚ // a ∈ leading} → Color) degree hdegree (alignmentEncodedWords words)
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_target_finite_word_choices.{u, v} s T hT
    (fun e : E => e.val) leading (alignmentEncodedWords words) hr
  refine ⟨Ω.image (fun p => (p.1, alignmentSignedTemplate Subtype.val p.2)), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hpos q hq
  · intro G _ X _ q₀ b L hint hG palette x
    have hz : ∀ e : E, ∃ z : ℤ,
        (q₀ : ℚ) * alignmentLetterScalar b e.val = (z : ℚ) := by
      intro e
      obtain ⟨z, hz⟩ := hint e.val e.property
      exact ⟨z, hz.symm⟩
    choose z hz using hz
    obtain ⟨p, hp, hreq⟩ := hΩ G X q₀ b L z hz hG palette x
    rw [alignmentEncodedWords_decode] at hreq
    exact ⟨_, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hreq⟩

end Hindman168
