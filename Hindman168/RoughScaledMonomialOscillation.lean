import Hindman168.RoughMonomialOscillation

namespace Hindman168
open scoped BigOperators

theorem rough_monomial_rescale {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (a : ℝ) (x : κ → ℝ) {Z : ℝ} (hZ : Z ≠ 0) :
    MvPolynomial.eval x (MvPolynomial.monomial I a) =
      (a * Z ^ (∑ j, I j)) * ∏ j, (x j * Z⁻¹) ^ I j := by
  rw [rough_monomial_eval_finite]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc
    a * ∏ j, x j ^ I j = (a * ∏ j, x j ^ I j) * (Z * Z⁻¹) ^ (∑ j, I j) := by
      rw [mul_inv_cancel₀ hZ, one_pow, mul_one]
    _ = _ := by rw [mul_pow]; ring

theorem rough_scaled_monomial_oscillation {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (a : ℝ) (x y : κ → ℝ) {A C Z δ : ℝ}
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (ha : |a| ≤ A * Z⁻¹ ^ (∑ j, I j))
    (hx : ∀ j, |x j| ≤ C * Z) (hy : ∀ j, |y j| ≤ C * Z)
    (hxy : ∀ j, |x j - y j| ≤ δ * Z) :
    |MvPolynomial.eval x (MvPolynomial.monomial I a) -
      MvPolynomial.eval y (MvPolynomial.monomial I a)| ≤
      (∑ j, I j : ℕ) * A * δ * C ^ (∑ j, I j) := by
  have hn (v : κ → ℝ) (hv : ∀ j, |v j| ≤ C * Z) :
      ∀ j, |v j * Z⁻¹| ≤ C := by
    intro j
    rw [abs_mul, abs_of_pos (inv_pos.mpr hZ)]
    calc
      |v j| * Z⁻¹ ≤ (C * Z) * Z⁻¹ :=
        mul_le_mul_of_nonneg_right (hv j) (inv_nonneg.mpr hZ.le)
      _ = C := by rw [mul_assoc, mul_inv_cancel₀ hZ.ne', mul_one]
  have hdiff : ∀ j, |x j * Z⁻¹ - y j * Z⁻¹| ≤ δ := by
    intro j
    rw [← sub_mul, abs_mul, abs_of_pos (inv_pos.mpr hZ)]
    calc
      |x j - y j| * Z⁻¹ ≤ (δ * Z) * Z⁻¹ :=
        mul_le_mul_of_nonneg_right (hxy j) (inv_nonneg.mpr hZ.le)
      _ = δ := by rw [mul_assoc, mul_inv_cancel₀ hZ.ne', mul_one]
  have hp := rough_finite_monomial_oscillation Finset.univ I
    (fun j => x j * Z⁻¹) (fun j => y j * Z⁻¹) C δ hC hδ
    (fun j _ => hn x hx j) (fun j _ => hn y hy j) (fun j _ => hdiff j)
  have hm : |a * Z ^ (∑ j, I j)| ≤ A := by
    rw [abs_mul, abs_of_pos (pow_pos hZ _)]
    calc
      |a| * Z ^ (∑ j, I j) ≤ (A * Z⁻¹ ^ (∑ j, I j)) * Z ^ (∑ j, I j) := by gcongr
      _ = A := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hZ.ne', one_pow, mul_one]
  rw [rough_monomial_rescale I a x hZ.ne', rough_monomial_rescale I a y hZ.ne',
    ← mul_sub, abs_mul]
  calc
    _ ≤ A * ((∑ j, I j : ℕ) * δ * C ^ (∑ j, I j)) :=
      mul_le_mul hm hp (abs_nonneg _) hA
    _ = _ := by ring

end Hindman168
