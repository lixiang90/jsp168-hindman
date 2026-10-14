import Hindman168.AlignmentFiniteDenominators
import Hindman168.AlignmentMonomialWords

/-! The actual inflated Alignment word is an ordered monomial word once
the finite plan's common denominator has made its old exponents integral. -/

namespace Hindman168

theorem alignment_inflated_word_monomial {n : ℕ} {i : Fin n} {G : Type*}
    [Group G] (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (T : Finset (Fin n)) (w : List (AlignmentAddingPair n i × ℚ))
    (z : AlignmentAddingPair n i × ℚ → ℤ)
    (hz : ∀ l ∈ w, (q₀ : ℚ) * alignmentLetterScalar b l = (z l : ℚ)) (k : ℕ) :
    alignmentWordValue q₀ b L (alignmentInflateWord T k w) =
      alignmentMonomialWord (fun l => L l.1 ^ z l)
        (fun l => (alignmentPairInflationExponent l.1 T).toNat) w k := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have hl := hz l List.mem_cons_self
    have hw : ∀ a ∈ w, (q₀ : ℚ) * alignmentLetterScalar b a = (z a : ℚ) :=
      fun a ha => hz a (List.mem_cons_of_mem l ha)
    change L l.1 ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b
        (l.1, l.2 * (k : ℚ) ^ alignmentPairInflationExponent l.1 T)⌋ *
        alignmentWordValue q₀ b L (alignmentInflateWord T k w) = _
    rw [alignmentLetter_integral_inflation_power q₀ b L l.1 l.2 T k (z l) hl, ih hw]
    rfl

theorem alignment_mapped_inflated_word_monomial {n : ℕ} {i : Fin n}
    {E G : Type*} [Group G] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (T : Finset (Fin n))
    (letter : E → AlignmentAddingPair n i × ℚ) (z : E → ℤ)
    (hz : ∀ e, (q₀ : ℚ) * alignmentLetterScalar b (letter e) = (z e : ℚ))
    (w : List E) (k : ℕ) :
    alignmentWordValue q₀ b L (alignmentInflateWord T k (w.map letter)) =
      alignmentMonomialWord (fun e => L (letter e).1 ^ z e)
        (fun e => (alignmentPairInflationExponent (letter e).1 T).toNat) w k := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    change L (letter e).1 ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b
        ((letter e).1, (letter e).2 * (k : ℚ) ^
          alignmentPairInflationExponent (letter e).1 T)⌋ *
        alignmentWordValue q₀ b L (alignmentInflateWord T k (w.map letter)) = _
    rw [alignmentLetter_integral_inflation_power q₀ b L (letter e).1 (letter e).2
      T k (z e) (hz e), ih]
    rfl

theorem alignment_updated_word_monomial {n : ℕ} {i : Fin n}
    {E G : Type*} [Group G] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (T : Finset (Fin n))
    (letter : E → AlignmentAddingPair n i × ℚ) (z : E → ℤ)
    (hz : ∀ e, (q₀ : ℚ) * alignmentLetterScalar b (letter e) = (z e : ℚ))
    (w : List E) (k : ℕ) (hk : 0 < k) :
    alignmentWordValue q₀ (alignmentScaleUpdate i T k b) L (w.map letter) =
      alignmentMonomialWord (fun e => L (letter e).1 ^ z e)
        (fun e => (alignmentPairInflationExponent (letter e).1 T).toNat) w k := by
  rw [alignmentWordValue_inflation q₀ b L T k hk,
    alignment_mapped_inflated_word_monomial q₀ b L T letter z hz]

end Hindman168
