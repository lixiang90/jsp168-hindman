import Hindman168.AlignmentWordInflation
import Hindman168.RationalPolynomialIntegerDilation

/-! One positive integer clears all actual rational letter exponents in
any prescribed finite scale/letter family. On these exponents the floor
interpretation is exactly integral; it also respects signed inverses.
Inflated letters are powers of the same old-scale generators, with
positive polynomial degrees and identity at parameter zero. -/

namespace Hindman168
open scoped Classical

theorem alignment_finite_letter_denominators {n : ℕ} {i : Fin n}
    (B : Finset (Fin n → ℚ)) (letters : Finset (AlignmentAddingPair n i × ℚ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ b ∈ B, ∀ l ∈ letters,
      (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨q₀, hq, h⟩ := rational_finite_family_integer_multiplier (B.product letters)
    (fun p => alignmentLetterScalar p.1 p.2)
  exact ⟨q₀, hq, fun b hb l hl => h (b, l) (Finset.mem_product.mpr ⟨hb, hl⟩)⟩

theorem alignmentLetter_value_of_integer {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (l : AlignmentAddingPair n i × ℚ) (z : ℤ)
    (hz : (q₀ : ℚ) * alignmentLetterScalar b l = (z : ℚ)) :
    L l.1 ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b l⌋ = L l.1 ^ z := by
  rw [hz, Int.floor_intCast]

theorem alignmentLetter_integral_inverse {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (e : AlignmentAddingPair n i) (γ : ℚ)
    (hint : (q₀ : ℚ) * alignmentLetterScalar b (e, γ) ∈ (Int.castRingHom ℚ).range) :
    L e ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b (e, -γ)⌋ =
      (L e ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b (e, γ)⌋)⁻¹ := by
  obtain ⟨z, hz⟩ := hint
  change (z : ℚ) = (q₀ : ℚ) * alignmentLetterScalar b (e, γ) at hz
  have hn : (q₀ : ℚ) * alignmentLetterScalar b (e, -γ) =
      -((q₀ : ℚ) * alignmentLetterScalar b (e, γ)) := by
    unfold alignmentLetterScalar
    ring
  rw [hn, ← hz, ← Int.cast_neg, Int.floor_intCast, Int.floor_intCast, zpow_neg]

theorem alignmentLetter_integral_inflation_power {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (e : AlignmentAddingPair n i) (γ : ℚ) (T : Finset (Fin n)) (k : ℕ) (z : ℤ)
    (hz : (q₀ : ℚ) * alignmentLetterScalar b (e, γ) = (z : ℚ)) :
    L e ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b
        (e, γ * (k : ℚ) ^ alignmentPairInflationExponent e T)⌋ =
      (L e ^ z) ^ (k ^ (alignmentPairInflationExponent e T).toNat) := by
  let d := (alignmentPairInflationExponent e T).toNat
  have hd : (d : ℤ) = alignmentPairInflationExponent e T :=
    Int.toNat_of_nonneg (alignmentPairInflationExponent_positive e T).le
  have hr : (q₀ : ℚ) * alignmentLetterScalar b
      (e, γ * (k : ℚ) ^ alignmentPairInflationExponent e T) =
      ((z * (k ^ d : ℕ) : ℤ) : ℚ) := by
    calc
      _ = ((q₀ : ℚ) * alignmentLetterScalar b (e, γ)) *
          (k : ℚ) ^ alignmentPairInflationExponent e T := by
        unfold alignmentLetterScalar
        ring
      _ = (z : ℚ) * (k : ℚ) ^ alignmentPairInflationExponent e T := by rw [hz]
      _ = _ := by
        rw [← hd, zpow_natCast]
        push_cast
        rfl
  rw [hr, Int.floor_intCast, zpow_mul, zpow_natCast]

theorem alignmentWord_inflated_zero {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (T : Finset (Fin n)) (w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentWordValue q₀ b L (alignmentInflateWord T 0 w) = 1 := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rcases l with ⟨e, γ⟩
    have hz : (0 : ℚ) ^ alignmentPairInflationExponent e T = 0 :=
      zero_zpow _ (ne_of_gt (alignmentPairInflationExponent_positive e T))
    change L e ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b
      (e, γ * (0 : ℚ) ^ alignmentPairInflationExponent e T)⌋ *
      alignmentWordValue q₀ b L (alignmentInflateWord T 0 w) = 1
    simpa only [hz, mul_zero, alignmentLetterScalar, zero_mul, Int.floor_zero, zpow_zero, one_mul] using ih

end Hindman168
