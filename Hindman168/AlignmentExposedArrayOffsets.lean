import Hindman168.AlignmentExposedResidues
import Hindman168.AlignmentIntegerArrayArguments

namespace Hindman168
open scoped BigOperators Classical

def alignmentPivotArrayResidue {n : ℕ} (t : Fin n → ℕ) (T : Finset (Fin n))
    (M : ℕ) (r₀ shift : ℤ) : ℤ :=
  ((alignmentNaturalBlockProduct t T : ℤ) * (r₀ + shift)) % M

noncomputable def alignmentPairProgression {n : ℕ} {i : Fin n} (q₀ w M : ℕ)
    (e : AlignmentAddingPair n i) (t : Fin n → ℕ) : ℤ :=
  alignmentProgressionShift (alignmentIntegerNumerator q₀ w e t)
    (alignmentNaturalBlockProduct t e.targetTail) (alignmentPairResidue q₀ w M e t) M

theorem alignmentRawExposure_tail_modEq {n : ℕ} {i : Fin n} {L M : ℕ}
    {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (h : alignmentRawExposure i L T t t') (hT : ∀ j ∈ T, j < i) (hML : M ∣ L) :
    Int.ModEq M (alignmentNaturalBlockProduct t T) (alignmentNaturalBlockProduct t' T) := by
  have hn := alignmentNaturalBlockProduct_modEq t t' T L
    (fun j hj => alignmentRawExposure_earlier_modEq h j (hT j hj))
  have hz : Int.ModEq L (alignmentNaturalBlockProduct t T) (alignmentNaturalBlockProduct t' T) :=
    Int.natCast_modEq_iff.mpr hn
  have hd : (M : ℤ) ∣ (L : ℤ) := by exact_mod_cast hML
  exact hz.of_dvd hd

theorem alignmentRawExposure_arrayResidue_eq {n : ℕ} {i : Fin n} {L M : ℕ}
    {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (h : alignmentRawExposure i L T t t') (hT : ∀ j ∈ T, j < i) (hML : M ∣ L)
    (r₀ shift : ℤ) :
    alignmentPivotArrayResidue t T M r₀ shift = alignmentPivotArrayResidue t' T M r₀ shift :=
  (alignmentRawExposure_tail_modEq h hT hML).mul_right (r₀ + shift)

theorem alignmentPairProgression_exact {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (t : Fin n → ℕ)
    (ht : ∀ j, Nat.Coprime (t j) (primorial w)) {i : Fin n}
    (e : AlignmentAddingPair n i) :
    (F.modulus w : ℤ) * alignmentPairProgression q₀ w (F.modulus w) e t =
      (alignmentIntegerNumerator q₀ w e t : ℤ) -
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * alignmentPairResidue q₀ w (F.modulus w) e t := by
  have hdata := alignmentPairResidue_master_data hF hq hw t ht e
  have hid := hdata.2.2.2.2.2 0 1
  simp only [zero_add, one_mul, mul_zero] at hid
  unfold alignmentPairProgression
  linear_combination hid

theorem alignmentRawExposure_progression_difference {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    {i : Fin n} {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (ht : ∀ j, Nat.Coprime (t j) (primorial w))
    (ht' : ∀ j, Nat.Coprime (t' j) (primorial w))
    (h : alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T t t')
    (e : AlignmentAddingPair n i) (he : e.targetTail = T) :
    (F.modulus w : ℤ) * (alignmentPairProgression q₀ w (F.modulus w) e t' -
      alignmentPairProgression q₀ w (F.modulus w) e t) =
      -((alignmentNaturalBlockProduct t' T : ℤ) - alignmentNaturalBlockProduct t T) *
        alignmentPairResidue q₀ w (F.modulus w) e t := by
  have ha := alignmentPairProgression_exact hF hq hw t ht e
  have hb := alignmentPairProgression_exact hF hq hw t' ht' e
  have hρ := alignmentRawExposure_pairResidue_eq hF q₀ w ht ht' h e
  have hQ := alignmentRawExposure_own_numerator_eq q₀ w h e he
  rw [← hρ, ← hQ] at hb
  rw [he] at ha hb
  linear_combination hb - ha

theorem alignmentRawExposure_arrayProgression_difference {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w)
    {i : Fin n} {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (ht : ∀ j, Nat.Coprime (t j) (primorial w))
    (ht' : ∀ j, Nat.Coprime (t' j) (primorial w))
    (h : alignmentRawExposure i ((F.modulus w : ℕ) * (primorial w) ^ w) T t t')
    (u : AlignmentAddingPair n i → ℤ) :
    (F.modulus w : ℤ) *
      (alignmentIntegerArrayProgression (fun e => alignmentPairProgression q₀ w (F.modulus w) e t') T u -
        alignmentIntegerArrayProgression (fun e => alignmentPairProgression q₀ w (F.modulus w) e t) T u) =
      -((alignmentNaturalBlockProduct t' T : ℤ) - alignmentNaturalBlockProduct t T) *
        alignmentIntegerArrayProgression
          (fun e => (alignmentPairResidue q₀ w (F.modulus w) e t : ℤ)) T u := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerArrayProgression
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.targetTail = T
  · rw [if_pos he, if_pos he, if_pos he]
    have hd := alignmentRawExposure_progression_difference hF hq hw ht ht' h e he
    linear_combination (u e) * hd
  · simp only [if_neg he, mul_zero, sub_self]

end Hindman168
