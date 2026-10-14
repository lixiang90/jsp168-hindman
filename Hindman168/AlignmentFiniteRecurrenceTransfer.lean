import Hindman168.AlignmentColoringCompactness
import Hindman168.AlignmentMonomialWords

/-! A uniform finite recurrence table in the free nilpotent group transfers
to every interpretation of its generators and every action. Polynomial
recurrence in the free group is an explicit, still unproved premise. -/

namespace Hindman168
universe u v w
open scoped Classical

theorem alignment_uniform_monomial_alternatives {E Color : Type u}
    [Finite Color] (s : ℕ) (degree : E → ℕ) (words : Finset (List E))
    (hrec : ∀ χ : AlignmentFreeNilpotent E s → Color, ∃ k J,
      0 < k ∧ ∀ w ∈ words, χ J =
        χ (alignmentMonomialWord (alignmentFreeGenerator s) degree w k * J)) :
    ∃ alternatives : Finset (ℕ × AlignmentFreeNilpotent E s),
      (∀ p ∈ alternatives, 0 < p.1) ∧
      ∀ (G : Type v) [Group G] (L : E → G)
        (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (χ : G → Color),
        ∃ p ∈ alternatives, ∀ w ∈ words,
          χ (alignmentFreeInterpretation s L hG p.2) =
            χ (alignmentMonomialWord L degree w p.1 *
              alignmentFreeInterpretation s L hG p.2) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_finite_coloring_alternatives words
    (alignmentMonomialWord (alignmentFreeGenerator s) degree) hrec
  refine ⟨Ω, hpos, ?_⟩
  intro G _ L hG χ
  obtain ⟨p, hp, hχ⟩ := hΩ (χ ∘ alignmentFreeInterpretation s L hG)
  refine ⟨p, hp, ?_⟩
  intro w hw
  simpa only [Function.comp_apply, map_mul, alignmentMonomialWord_interpretation]
    using hχ w hw

theorem alignment_uniform_action_alternatives {E Color : Type u} [Finite Color]
    (s : ℕ) (degree : E → ℕ) (words : Finset (List E))
    (hrec : ∀ χ : AlignmentFreeNilpotent E s → Color, ∃ k J,
      0 < k ∧ ∀ w ∈ words, χ J =
        χ (alignmentMonomialWord (alignmentFreeGenerator s) degree w k * J)) :
    ∃ alternatives : Finset (ℕ × AlignmentFreeNilpotent E s),
      (∀ p ∈ alternatives, 0 < p.1) ∧
      ∀ (G : Type v) [Group G] (X : Type w) [MulAction G X]
        (L : E → G) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (palette : X → Color) (x : X),
        ∃ p ∈ alternatives, ∀ w ∈ words,
          palette (alignmentFreeInterpretation s L hG p.2 • x) =
            palette (alignmentMonomialWord L degree w p.1 •
              (alignmentFreeInterpretation s L hG p.2 • x)) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_uniform_monomial_alternatives.{u, v}
    s degree words hrec
  refine ⟨Ω, hpos, ?_⟩
  intro G _ X _ L hG palette x
  obtain ⟨p, hp, hχ⟩ := hΩ G L hG (fun g => palette (g • x))
  refine ⟨p, hp, ?_⟩
  intro w hw
  simpa only [mul_smul] using hχ w hw

theorem alignment_recurrence_handedness {G W Color : Type*} [Group G]
    (words : Finset W) (curve : W → ℕ → G)
    (hleft : ∀ χ : G → Color, ∃ k J,
      0 < k ∧ ∀ w ∈ words, χ J = χ (J * (curve w k)⁻¹)) :
    ∀ χ : G → Color, ∃ k J,
      0 < k ∧ ∀ w ∈ words, χ J = χ (curve w k * J) := by
  intro χ
  obtain ⟨k, J, hk, hJ⟩ := hleft (fun g => χ g⁻¹)
  refine ⟨k, J⁻¹, hk, ?_⟩
  intro w hw
  simpa only [mul_inv_rev, inv_inv] using hJ w hw

end Hindman168
