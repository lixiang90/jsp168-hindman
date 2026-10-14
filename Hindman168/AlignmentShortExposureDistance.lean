import Hindman168.AlignmentShortExposureKey
import Hindman168.AlignmentNumericalPolynomialBounds

namespace Hindman168

open scoped BigOperators Classical

theorem alignment_same_nat_bin_distance {a b R : ℕ} (hR : 0 < R)
    (h : a / R = b / R) : |(a : ℤ) - b| ≤ (R : ℤ) := by
  have ha := Nat.mod_add_div a R
  have hb := Nat.mod_add_div b R
  have har := Nat.mod_lt a hR
  have hbr := Nat.mod_lt b hR
  rw [h] at ha
  have hab : a ≤ b + R := by omega
  have hba : b ≤ a + R := by omega
  have habz : (a : ℤ) ≤ b + (R : ℤ) := by exact_mod_cast hab
  have hbaz : (b : ℤ) ≤ a + (R : ℤ) := by exact_mod_cast hba
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem alignmentShortExposureKey_product_distance
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2)
    (hpos : ∀ j ∈ T, 0 < x j)
    (hR : 0 < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y) :
    |((alignmentNaturalBlockProduct y T * y i : ℕ) : ℤ) -
      ((alignmentNaturalBlockProduct x T * x i : ℕ) : ℤ)| ≤
      (F.auxiliary w i.val * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ) := by
  have hl : (∏ j ∈ T, 2 ^ Nat.log2 (x j)) ≤ F.auxiliary w i.val :=
    (Finset.prod_le_prod' (fun j hj => Nat.log2_self_le (hpos j hj).ne')).trans
      (alignment_earlier_block_product_bound hF w i x hx T hT)
  have hwidth : 0 < (∏ j ∈ T, 2 ^ Nat.log2 (x j)) *
      alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) :=
    Nat.mul_pos (Finset.prod_pos (fun _ _ => Nat.pow_pos (by decide))) hR
  have hd := alignment_same_nat_bin_distance hwidth
    (alignmentShortExposureKey_product_bin F w i T hkey).symm
  exact hd.trans (by exact_mod_cast (Nat.mul_le_mul_right
    (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) hl))

end Hindman168
