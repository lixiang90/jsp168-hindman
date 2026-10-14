import Hindman168.AlignmentTargetAlternatives

/-! Free nilpotent jumps have signed word representatives, chosen before
their generators acquire numerical values. Their interpretation is exactly
the original rational-letter word after the integral exponents are fixed. -/

namespace Hindman168
universe u v
open scoped Classical

def alignmentFreeSignedWord {E : Type*} (s : ℕ) (w : List (E × Bool)) :
    AlignmentFreeNilpotent E s :=
  QuotientGroup.mk' ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s) (FreeGroup.mk w)

def alignmentSignedTemplate {n : ℕ} {i : Fin n} {E : Type*}
    (letter : E → AlignmentAddingPair n i × ℚ) (w : List (E × Bool)) :
    List (AlignmentAddingPair n i × ℚ) :=
  w.map (fun l => ((letter l.1).1, cond l.2 (letter l.1).2 (-(letter l.1).2)))

theorem alignmentFreeSignedWord_surjective (E : Type*) (s : ℕ) :
    Function.Surjective (alignmentFreeSignedWord (E := E) s) := by
  intro J
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    ((⊤ : Subgroup (FreeGroup E)).lowerCentralSeries s) J
  obtain ⟨w, hw⟩ := Quot.exists_rep g
  change FreeGroup.mk w = g at hw
  refine ⟨w, ?_⟩
  unfold alignmentFreeSignedWord
  rw [hw]
  exact hg

theorem alignment_finite_signed_jump_representatives {E : Type*} (s : ℕ)
    (alternatives : Finset (ℕ × AlignmentFreeNilpotent E s))
    (hpos : ∀ p ∈ alternatives, 0 < p.1) :
    ∃ lifts : Finset (ℕ × List (E × Bool)),
      (∀ p ∈ lifts, 0 < p.1) ∧
      lifts.image (fun p => (p.1, alignmentFreeSignedWord s p.2)) = alternatives := by
  choose rep hrep using alignmentFreeSignedWord_surjective E s
  refine ⟨alternatives.image (fun p => (p.1, rep p.2)), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hpos q hq
  · rw [Finset.image_image]
    simp only [Function.comp_def]
    have hfun : (fun p : ℕ × AlignmentFreeNilpotent E s =>
        (p.1, alignmentFreeSignedWord s (rep p.2))) = id := by
      funext p
      exact Prod.ext rfl (hrep p.2)
    rw [hfun, Finset.image_id]

theorem alignment_signed_jump_interpretation {n : ℕ} {i : Fin n}
    {E G : Type*} [Group G] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (letter : E → AlignmentAddingPair n i × ℚ)
    (z : E → ℤ) (hz : ∀ e, (q₀ : ℚ) * alignmentLetterScalar b (letter e) = (z e : ℚ))
    (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (w : List (E × Bool)) :
    alignmentFreeInterpretation s (fun e => L (letter e).1 ^ z e) hG
      (alignmentFreeSignedWord s w) =
      alignmentWordValue q₀ b L (alignmentSignedTemplate letter w) := by
  change FreeGroup.lift (fun e => L (letter e).1 ^ z e) (FreeGroup.mk w) = _
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rcases l with ⟨e, sign⟩
    cases sign with
    | false =>
      have hint : (q₀ : ℚ) * alignmentLetterScalar b (letter e) ∈
          (Int.castRingHom ℚ).range := ⟨z e, (hz e).symm⟩
      simp only [alignmentSignedTemplate, List.map_cons, List.prod_cons,
        Bool.cond_false, alignmentWordValue] at ih ⊢
      rw [alignmentLetter_integral_inverse q₀ b L (letter e).1 (letter e).2 hint,
        alignmentLetter_value_of_integer q₀ b L (letter e) (z e) (hz e), ih]
    | true =>
      simp only [alignmentSignedTemplate, List.map_cons, List.prod_cons,
        Bool.cond_true, alignmentWordValue] at ih ⊢
      rw [alignmentLetter_value_of_integer q₀ b L (letter e) (z e) (hz e), ih]

theorem alignment_target_finite_word_choices {n : ℕ} {i : Fin n}
    {E Color : Type} [Finite Color]
    (s : ℕ) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (letter : E → AlignmentAddingPair n i × ℚ)
    (leading : Finset ℚ) (words : Finset (List E))
    (hrec : ∀ χ : AlignmentFreeNilpotent E s → ({a : ℚ // a ∈ leading} → Color),
      ∃ k J, 0 < k ∧ ∀ w ∈ words, χ J = χ
        (alignmentMonomialWord (alignmentFreeGenerator s)
          (fun e => (alignmentPairInflationExponent (letter e).1 T).toNat) w k * J)) :
    ∃ choices : Finset (ℕ × List (E × Bool)),
      (∀ p ∈ choices, 0 < p.1) ∧
      ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
        (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G) (z : E → ℤ),
        (∀ e, (q₀ : ℚ) * alignmentLetterScalar b (letter e) = (z e : ℚ)) →
        ∀ (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
          (palette : ℚ → X → Color) (x : X), ∃ p ∈ choices,
          alignmentPaletteRequirement q₀ (alignmentScaleUpdate i T p.1 b) L
            (insert i T) palette leading (words.image (List.map letter))
            (alignmentWordValue q₀ b L (alignmentSignedTemplate letter p.2) • x) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_target_finite_alternatives.{u, v}
    s T hT letter leading words hrec
  obtain ⟨choices, hchoices, himage⟩ := alignment_finite_signed_jump_representatives s Ω hpos
  refine ⟨choices, hchoices, ?_⟩
  intro G _ X _ q₀ b L z hz hG palette x
  obtain ⟨p, hp, hreq⟩ := hΩ G X q₀ b L z hz hG palette x
  rw [← himage] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rw [alignment_signed_jump_interpretation q₀ b L letter z hz s hG] at hreq
  exact ⟨q, hq, hreq⟩

end Hindman168
