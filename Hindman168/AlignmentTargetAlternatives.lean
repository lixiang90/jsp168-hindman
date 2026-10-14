import Hindman168.AlignmentFiniteRecurrenceTransfer
import Hindman168.AlignmentIntegralMonomialWords

/-! Uniform alternatives for the actual palette requirement at a target.
The free-group recurrence premise precedes all rational scales, integral
letter values, acting generators, palettes and centers. -/

namespace Hindman168
universe u v
open scoped Classical

theorem alignment_target_finite_alternatives {n : ℕ} {i : Fin n}
    {E Color : Type} [Finite Color]
    (s : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (letter : E → AlignmentAddingPair n i × ℚ)
    (leading : Finset ℚ) (words : Finset (List E))
    (hrec : ∀ χ : AlignmentFreeNilpotent E s → ({a : ℚ // a ∈ leading} → Color),
      ∃ k J, 0 < k ∧ ∀ w ∈ words, χ J = χ
        (alignmentMonomialWord (alignmentFreeGenerator s)
          (fun e => (alignmentPairInflationExponent (letter e).1 T).toNat) w k * J)) :
    ∃ alternatives : Finset (ℕ × AlignmentFreeNilpotent E s),
      (∀ p ∈ alternatives, 0 < p.1) ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G) (z : E → ℤ),
        (∀ e, (q₀ : ℚ) * alignmentLetterScalar b (letter e) = (z e : ℚ)) →
        ∀ (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
          (palette : ℚ → X → Color) (x : X), ∃ p ∈ alternatives,
          alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T p.1 b) L
            (insert i T) palette leading (words.image (List.map letter))
            (alignmentFreeInterpretation s (fun e => L (letter e).1 ^ z e) hG p.2 • x) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_uniform_action_alternatives.{0, u, v} s
    (fun e => (alignmentPairInflationExponent (letter e).1 T).toNat) words hrec
  refine ⟨Ω, hpos, ?_⟩
  intro G _ X _ q₀ b L z hz hG palette x
  obtain ⟨p, hp, hχ⟩ := hΩ G X (fun e => L (letter e).1 ^ z e) hG
    (fun y a => palette (a.val * finiteScaleBlockProduct b (insert i T)) y) x
  refine ⟨p, hp, ?_⟩
  intro a ha v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  have h := congrFun (hχ w hw) ⟨a, ha⟩
  rw [alignmentScaleUpdate_target_fixed i T p.1 (hpos p hp) hT b,
    alignment_updated_word_monomial q₀ b L T letter z hz w p.1 (hpos p hp)]
  exact h

end Hindman168
