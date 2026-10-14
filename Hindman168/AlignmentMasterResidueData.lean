import Hindman168.AlignmentIntegerResidues
import Hindman168.AlignmentIntegerNumerators

namespace Hindman168
open Filter
open scoped Topology

theorem alignmentMaster_tail_coprime {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (t : Fin n → ℕ)
    (S : Finset (Fin n)) (hunit : ∀ j ∈ S, Nat.Coprime (t j) (primorial w)) :
    Nat.Coprime (alignmentNaturalBlockProduct t S)
      ((F.modulus w : ℕ) * (primorial w) ^ w) := by
  obtain ⟨E, hE⟩ := hF.smooth_modulus w
  have ht := alignmentNaturalBlockProduct_coprime t S (primorial w) hunit
  rw [hE, ← pow_add]
  exact ht.pow_right _

theorem alignmentMaster_integer_residue_data {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (t : Fin n → ℕ)
    (hunit : ∀ j, Nat.Coprime (t j) (primorial w)) {i : Fin n}
    (e : AlignmentAddingPair n i) :
    ∃ ρ : ℕ, ρ < (F.modulus w : ℕ) * (primorial w) ^ w ∧
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
  have hM : 0 < (F.modulus w : ℕ) := (F.modulus w).pos
  have hV : 0 < (primorial w) ^ w := Nat.pow_pos (primorial_pos w)
  have hW : primorial w ∣ (primorial w) ^ w := by
    simpa only [pow_one] using (pow_dvd_pow (primorial w) (by omega : 1 ≤ w))
  have hWL : primorial w ∣ (F.modulus w : ℕ) * (primorial w) ^ w :=
    hW.trans (dvd_mul_left _ _)
  obtain ⟨ρ, hρ, hWρ, hcong, hexact, hVΔ⟩ := alignment_bounded_residue_shift
    (alignmentIntegerNumerator q₀ w e t) (alignmentNaturalBlockProduct t e.targetTail)
    (F.modulus w) ((primorial w) ^ w) (primorial w) hM hV
    (alignmentMaster_tail_coprime hF w t e.targetTail (fun j _ => hunit j)) hWL
    (alignmentIntegerNumerator_divisible hq hw e t)
  have hVM := Nat.le_of_dvd hM (hF.primorial_power_dvd w)
  refine ⟨ρ, hρ, hρ.trans_le ?_, hWρ, ?_, ?_, ?_⟩
  · simpa only [pow_two] using Nat.mul_le_mul_left (F.modulus w : ℕ) hVM
  · simpa only [Nat.cast_pow] using hcong
  · simpa only [Nat.cast_pow] using hVΔ
  · exact alignment_integer_displacement_identity hexact

theorem alignmentMaster_eventual_residue_divisibility {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ k : ℕ}
    (hq : 0 < q₀) (hk : 0 < k) :
    ∀ᶠ w in atTop, ∀ t : Fin n → ℕ,
      (∀ j, Nat.Coprime (t j) (primorial w)) → ∀ i : Fin n,
      ∀ e : AlignmentAddingPair n i,
      ∃ ρ : ℕ, ρ < (F.modulus w : ℕ) ^ 2 ∧ primorial w ∣ ρ ∧
        (k : ℤ) ∣ alignmentProgressionShift (alignmentIntegerNumerator q₀ w e t)
          (alignmentNaturalBlockProduct t e.targetTail) ρ (F.modulus w) ∧
        ∀ p m : ℤ,
          (alignmentNaturalBlockProduct t e.targetTail : ℤ) * (p + m * ρ) +
            m * (F.modulus w : ℤ) * alignmentProgressionShift
              (alignmentIntegerNumerator q₀ w e t)
              (alignmentNaturalBlockProduct t e.targetTail) ρ (F.modulus w) =
          (alignmentNaturalBlockProduct t e.targetTail : ℤ) * p +
            m * alignmentIntegerNumerator q₀ w e t := by
  filter_upwards [eventually_ge_atTop (q₀ + 1),
    fixed_integer_eventually_dvd_primorial_power hk.ne'] with w hw hkw
  intro t ht i e
  obtain ⟨ρ, _, hρ, hWρ, _, hVΔ, hidentity⟩ :=
    alignmentMaster_integer_residue_data hF hq hw t ht e
  have hkz : (k : ℤ) ∣ (primorial w : ℤ) ^ w := by exact_mod_cast hkw
  exact ⟨ρ, hρ, hWρ, hkz.trans hVΔ, hidentity⟩

end Hindman168
