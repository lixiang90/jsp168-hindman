import Hindman168.RoughScaledMonomials

namespace Hindman168
open scoped BigOperators Classical

noncomputable def roughErrorPolynomial {κ : Type*} (s : Finset (κ →₀ ℕ))
    (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) : MvPolynomial κ ℝ :=
  MvPolynomial.C a0 + ∑ I ∈ s, MvPolynomial.monomial I (a I)

theorem rough_error_polynomial_value_bound {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) (x : κ → ℝ)
    {A C Z : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z) (h0 : |a0| ≤ 1)
    (ha : ∀ I ∈ s, |a I| ≤ A * Z⁻¹ ^ (∑ j, I j)) (hx : ∀ j, |x j| ≤ C * Z) :
    |MvPolynomial.eval x (roughErrorPolynomial s a0 a)| ≤
      1 + ∑ I ∈ s, A * C ^ (∑ j, I j) := by
  rw [roughErrorPolynomial, MvPolynomial.eval_add, MvPolynomial.eval_C, MvPolynomial.eval_sum]
  apply (abs_add_le _ _).trans
  apply add_le_add h0
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  exact rough_scaled_monomial_bound I (a I) x hA hZ (ha I hI) hx

theorem rough_error_polynomial_pderiv_bound {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) (x : κ → ℝ) (j : κ)
    {A C Z : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z)
    (ha : ∀ I ∈ s, |a I| ≤ A * Z⁻¹ ^ (∑ k, I k)) (hx : ∀ k, |x k| ≤ C * Z) :
    |MvPolynomial.eval x (MvPolynomial.pderiv j (roughErrorPolynomial s a0 a))| ≤
      ∑ I ∈ s, (I j : ℝ) * A * C ^ ((∑ k, I k) - 1) * Z⁻¹ := by
  simp only [roughErrorPolynomial, map_add, map_sum, MvPolynomial.pderiv_C, zero_add]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  exact rough_scaled_monomial_pderiv_bound I j (a I) x hA hZ (ha I hI) hx

theorem rough_error_polynomial_box_bounds {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (q : ℕ) (hq : ∀ I ∈ s, (∑ j, I j) ≤ q)
    (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) (x : κ → ℝ)
    {A C Z : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (h0 : |a0| ≤ 1)
    (ha : ∀ I ∈ s, |a I| ≤ A * Z⁻¹ ^ (∑ j, I j)) (hx : ∀ j, |x j| ≤ C * Z) :
    |MvPolynomial.eval x (roughErrorPolynomial s a0 a)| ≤ 1 + (s.card : ℝ) * A * C ^ q ∧
      ∀ j, |MvPolynomial.eval x (MvPolynomial.pderiv j (roughErrorPolynomial s a0 a))| ≤
        ((s.card : ℝ) * q * A * C ^ q) * Z⁻¹ := by
  have hC0 : 0 ≤ C := by linarith
  constructor
  · apply (rough_error_polynomial_value_bound s a0 a x hA hZ h0 ha hx).trans
    have hs : (∑ I ∈ s, A * C ^ (∑ j, I j)) ≤ ∑ _I ∈ s, A * C ^ q := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (hq I hI)) hA
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using add_le_add_right hs 1
  · intro j
    apply (rough_error_polynomial_pderiv_bound s a0 a x j hA hZ ha hx).trans
    have hs : (∑ I ∈ s, (I j : ℝ) * A * C ^ ((∑ k, I k) - 1) * Z⁻¹) ≤
        ∑ _I ∈ s, (q : ℝ) * A * C ^ q * Z⁻¹ := by
      apply Finset.sum_le_sum
      intro I hI
      have hij : I j ≤ ∑ k, I k := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
      have hijq : (I j : ℝ) ≤ q := by exact_mod_cast hij.trans (hq I hI)
      have hpow := pow_le_pow_right₀ hC ((Nat.sub_le (∑ k, I k) 1).trans (hq I hI))
      gcongr
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hs

end Hindman168
