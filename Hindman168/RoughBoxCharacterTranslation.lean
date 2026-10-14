import Hindman168.RoughSignedTranslationCoefficients
import Hindman168.RoughModOneIntegerCombination

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

/-- The signed integer translation used to return a cube character to the
original box. The constant is uniform in every scalar coefficient. -/
theorem rough_box_character_translation_bound {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (θ : (κ → ℕ) → ℝ) (c : ℝ) (b : κ → ℤ)
    (q : ℕ) (Z C A : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hdegree : ∀ J ∈ s, (∑ j, J j) ≤ q) (hb : ∀ j, |(b j : ℝ)| ≤ C*Z)
    (hθ : ∀ J ∈ s, ‖(θ J : UnitAddCircle)‖ ≤ A*Z⁻¹^(∑ j, J j))
    (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    ‖((coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
        (MvPolynomial.C c+∑ J ∈ s, monomial (Finsupp.equivFunOnFinite.symm J) (θ J))) : ℝ) : UnitAddCircle)‖ ≤
      ((s.card : ℝ)*(2 : ℝ)^q*(max 1 C)^q*A)*Z⁻¹^(∑ j, I j) := by
  rw [rough_affine_positive_signed_coefficient s θ c b I hI]
  apply (rough_mod_one_integer_combination s (fun J => roughSignedBinomialWeight I J b) θ).trans
  have hterm : ∀ J ∈ s,
      |(roughSignedBinomialWeight I J b : ℝ)| * ‖(θ J : UnitAddCircle)‖ ≤
      ((2 : ℝ)^q*(max 1 C)^q*A)*Z⁻¹^(∑ j, I j) := by
    intro J hJ
    by_cases hIJ : ∀ j, I j ≤ J j
    · let n := (∑ j, J j)-(∑ j, I j)
      have he : (∑ j, I j)+n = ∑ j, J j := Nat.add_sub_cancel'
        (Finset.sum_le_sum fun j _ => hIJ j)
      have hnq : n ≤ q := (Nat.sub_le _ _).trans (hdegree J hJ)
      have hpow : C^n ≤ (max 1 C)^q :=
        (pow_le_pow_left₀ hC (le_max_right _ _) _).trans
          (pow_le_pow_right₀ (le_max_left _ _) hnq)
      have hzpow : Z^n*Z⁻¹^n = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
      have hw := roughSignedBinomialWeight_bound I J b q (C*Z)
        (mul_nonneg hC hZ.le) (hdegree J hJ) hb
      calc
        _ ≤ ((2 : ℝ)^q*(C*Z)^n)*(A*Z⁻¹^(∑ j, J j)) :=
          mul_le_mul hw (hθ J hJ) (norm_nonneg _) (by positivity)
        _ = ((2 : ℝ)^q*C^n*A)*Z⁻¹^(∑ j, I j) := by
          rw [← he, pow_add, mul_pow]
          calc
            _ = ((2 : ℝ)^q*C^n*A)*(Z^n*Z⁻¹^n)*Z⁻¹^(∑ j, I j) := by ring
            _ = _ := by rw [hzpow, mul_one]
        _ ≤ _ := by gcongr
    · rw [roughSignedBinomialWeight_eq_zero I J b hIJ, Int.cast_zero, abs_zero, zero_mul]
      positivity
  calc
    _ ≤ ∑ J ∈ s, ((2 : ℝ)^q*(max 1 C)^q*A)*Z⁻¹^(∑ j, I j) :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Hindman168
