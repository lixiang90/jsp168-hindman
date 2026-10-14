import Hindman168.AlignmentRawExposure
import Hindman168.AlignmentIntegerSlotShifts

namespace Hindman168

noncomputable def alignmentPairResidue {n : ℕ} {i : Fin n} (q₀ w M : ℕ)
    (e : AlignmentAddingPair n i) (t : Fin n → ℕ) : ℕ :=
  alignmentResidueRepresentative (alignmentIntegerNumerator q₀ w e t)
    (alignmentNaturalBlockProduct t e.targetTail) (M * (primorial w) ^ w)

theorem alignmentPairResidue_master_data {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (t : Fin n → ℕ)
    (hunit : ∀ j, Nat.Coprime (t j) (primorial w)) {i : Fin n}
    (e : AlignmentAddingPair n i) :
    let ρ := alignmentPairResidue q₀ w (F.modulus w) e t
    ρ < (F.modulus w : ℕ) * (primorial w) ^ w ∧
      ρ < (F.modulus w : ℕ) ^ 2 ∧ primorial w ∣ ρ ∧
      (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ ≡
        alignmentIntegerNumerator q₀ w e t
          [ZMOD (F.modulus w : ℤ) * (primorial w : ℤ) ^ w] ∧
      (primorial w : ℤ) ^ w ∣ alignmentProgressionShift
        (alignmentIntegerNumerator q₀ w e t)
        (alignmentNaturalBlockProduct t e.targetTail) ρ (F.modulus w) ∧
      ∀ p m : ℤ,
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * (p + m * ρ) +
          m * (F.modulus w : ℤ) * alignmentProgressionShift
            (alignmentIntegerNumerator q₀ w e t)
            (alignmentNaturalBlockProduct t e.targetTail) ρ (F.modulus w) =
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * p +
          m * alignmentIntegerNumerator q₀ w e t := by
  obtain ⟨ρ, hρ, hMρ, hWρ, hcong, hdiv, hid⟩ :=
    alignmentMaster_integer_residue_data hF hq hw t hunit e
  have ht := alignmentMaster_tail_coprime hF w t e.targetTail (fun j _ => hunit j)
  have hL : 0 < (F.modulus w : ℕ) * (primorial w) ^ w :=
    Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w))
  have hc : Nat.ModEq ((F.modulus w : ℕ) * (primorial w) ^ w)
      (alignmentNaturalBlockProduct t e.targetTail * ρ) (alignmentIntegerNumerator q₀ w e t) := by
    simpa only [← Nat.cast_pow, ← Nat.cast_mul, Int.natCast_modEq_iff] using hcong
  have hcanonical : alignmentPairResidue q₀ w (F.modulus w) e t = ρ :=
    alignmentResidueRepresentative_eq hL ht hρ hc
  dsimp only
  rw [hcanonical]
  exact ⟨hρ, hMρ, hWρ, hcong, hdiv, hid⟩

theorem alignmentRawExposure_pairResidue_eq {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ)
    {i : Fin n} {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (ht : ∀ j, Nat.Coprime (t j) (primorial w))
    (ht' : ∀ j, Nat.Coprime (t' j) (primorial w))
    (h : alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T t t')
    (e : AlignmentAddingPair n i) :
    alignmentPairResidue q₀ w (F.modulus w) e t =
      alignmentPairResidue q₀ w (F.modulus w) e t' := by
  apply alignmentResidueRepresentative_congr
    (Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w)))
    (alignmentMaster_tail_coprime hF w t e.targetTail (fun j _ => ht j))
    (alignmentMaster_tail_coprime hF w t' e.targetTail (fun j _ => ht' j))
  · exact alignmentNaturalBlockProduct_modEq t t' e.targetTail _
      (fun j hj => alignmentRawExposure_earlier_modEq h j (alignmentPair_target_before e j hj))
  · exact alignmentRawExposure_numerator_modEq q₀ w h e

theorem alignmentRawExposure_slot_shift_eq {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ)
    {i : Fin n} {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (ht : ∀ j, Nat.Coprime (t j) (primorial w))
    (ht' : ∀ j, Nat.Coprime (t' j) (primorial w))
    (h : alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T t t')
    (v : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e t) v =
      alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e t') v := by
  have heq : (fun e : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w) e t) =
      (fun e : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w) e t') := by
    funext e
    exact alignmentRawExposure_pairResidue_eq hF q₀ w ht ht' h e
  rw [heq]

end Hindman168
