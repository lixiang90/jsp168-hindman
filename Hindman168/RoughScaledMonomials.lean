import Hindman168.RoughBinomialWeights
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Hindman168
open scoped BigOperators Classical

theorem rough_scaled_product_error {a v A C Z : ℝ} (d r : ℕ)
    (hA : 0 ≤ A) (hZ : 0 < Z)
    (ha : |a| ≤ A * Z⁻¹ ^ (d + r)) (hv : |v| ≤ (C * Z) ^ d) :
    |a * v| ≤ A * C ^ d * Z⁻¹ ^ r := by
  rw [abs_mul]
  calc
    |a| * |v| ≤ (A * Z⁻¹ ^ (d + r)) * (C * Z) ^ d := by gcongr
    _ = A * C ^ d * (Z⁻¹ * Z) ^ d * Z⁻¹ ^ r := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hZ.ne', one_pow, mul_one]

theorem rough_monomial_product_bound {κ : Type*} [Fintype κ]
    (I : κ → ℕ) (x : κ → ℝ) (B : ℝ) (hx : ∀ j, |x j| ≤ B) :
    |∏ j, x j ^ I j| ≤ B ^ (∑ j, I j) := by
  rw [Finset.abs_prod]
  calc
    ∏ j, |x j ^ I j| ≤ ∏ j, B ^ I j := by
      apply Finset.prod_le_prod
      · intro j _; exact abs_nonneg _
      · intro j _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx j) _
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem rough_monomial_eval_finite {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (a : ℝ) (x : κ → ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial I a) = a * ∏ j, x j ^ I j := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem rough_scaled_monomial_bound {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (a : ℝ) (x : κ → ℝ) {A C Z : ℝ}
    (hA : 0 ≤ A) (hZ : 0 < Z)
    (ha : |a| ≤ A * Z⁻¹ ^ (∑ j, I j)) (hx : ∀ j, |x j| ≤ C * Z) :
    |MvPolynomial.eval x (MvPolynomial.monomial I a)| ≤ A * C ^ (∑ j, I j) := by
  rw [rough_monomial_eval_finite]
  have hh := rough_scaled_product_error (∑ j, I j) 0 hA hZ
    (by simpa only [Nat.add_zero] using ha) (rough_monomial_product_bound I x (C * Z) hx)
  simpa only [pow_zero, mul_one] using hh

theorem rough_multiindex_lower_degree {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (j : κ) (hj : 0 < I j) :
    (∑ k, (I - Finsupp.single j 1 : κ →₀ ℕ) k) + 1 = ∑ k, I k := by
  classical
  have hle : Finsupp.single j 1 ≤ I := by
    intro k
    by_cases hk : k = j
    · subst k; simpa using (Nat.succ_le_iff.mpr hj)
    · simp [hk]
  have hh := congrArg (fun J : κ →₀ ℕ => ∑ k, J k) (tsub_add_cancel_of_le hle)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hh
  simpa [Finsupp.single_apply] using hh

theorem rough_scaled_monomial_pderiv_bound {κ : Type*} [Fintype κ]
    (I : κ →₀ ℕ) (j : κ) (a : ℝ) (x : κ → ℝ) {A C Z : ℝ}
    (hA : 0 ≤ A) (hZ : 0 < Z)
    (ha : |a| ≤ A * Z⁻¹ ^ (∑ k, I k)) (hx : ∀ k, |x k| ≤ C * Z) :
    |MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial I a))| ≤
      (I j : ℝ) * A * C ^ ((∑ k, I k) - 1) * Z⁻¹ := by
  by_cases hj : I j = 0
  · simp [MvPolynomial.pderiv_monomial, hj]
  · have hdeg := rough_multiindex_lower_degree I j (Nat.pos_of_ne_zero hj)
    have hbound := rough_scaled_product_error (∑ k, (I - Finsupp.single j 1 : κ →₀ ℕ) k) 1 hA hZ
      (by simpa only [hdeg] using ha)
      (rough_monomial_product_bound (fun k => (I - Finsupp.single j 1 : κ →₀ ℕ) k) x (C * Z) hx)
    rw [MvPolynomial.pderiv_monomial, rough_monomial_eval_finite]
    have heq : (∑ k, (I - Finsupp.single j 1 : κ →₀ ℕ) k) = (∑ k, I k) - 1 := by omega
    rw [heq, pow_one] at hbound
    calc
      |(a * (I j : ℝ)) * ∏ k, x k ^ (I - Finsupp.single j 1 : κ →₀ ℕ) k| =
          (I j : ℝ) * |a * ∏ k, x k ^ (I - Finsupp.single j 1 : κ →₀ ℕ) k| := by
        rw [show (a * (I j : ℝ)) * _ = (I j : ℝ) * (a * ∏ k, x k ^ (I - Finsupp.single j 1 : κ →₀ ℕ) k) by ring,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg (I j))]
      _ ≤ (I j : ℝ) * (A * C ^ ((∑ k, I k) - 1) * Z⁻¹) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
      _ = _ := by ring

end Hindman168
