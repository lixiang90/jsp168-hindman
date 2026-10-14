import Hindman168.RoughScaledMonomialOscillation
import Hindman168.RoughSlowPolynomial

namespace Hindman168
open scoped BigOperators

theorem rough_error_polynomial_oscillation {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) (x y : κ → ℝ)
    {A C Z δ : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (ha : ∀ I ∈ s, |a I| ≤ A * Z⁻¹ ^ (∑ j, I j))
    (hx : ∀ j, |x j| ≤ C * Z) (hy : ∀ j, |y j| ≤ C * Z)
    (hxy : ∀ j, |x j - y j| ≤ δ * Z) :
    |MvPolynomial.eval x (roughErrorPolynomial s a0 a) -
      MvPolynomial.eval y (roughErrorPolynomial s a0 a)| ≤
      ∑ I ∈ s, (∑ j, I j : ℕ) * A * δ * C ^ (∑ j, I j) := by
  simp only [roughErrorPolynomial, map_add, MvPolynomial.eval_C, map_sum]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  exact rough_scaled_monomial_oscillation I (a I) x y hA hC hZ hδ (ha I hI) hx hy hxy

theorem rough_error_polynomial_subbox_oscillation {κ : Type*} [Fintype κ]
    (s : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ I ∈ s, (∑ j, I j) ≤ d)
    (a0 : ℝ) (a : (κ →₀ ℕ) → ℝ) (x y : κ → ℝ)
    {A C Z δ : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (ha : ∀ I ∈ s, |a I| ≤ A * Z⁻¹ ^ (∑ j, I j))
    (hx : ∀ j, |x j| ≤ C * Z) (hy : ∀ j, |y j| ≤ C * Z)
    (hxy : ∀ j, |x j - y j| ≤ δ * Z) :
    |MvPolynomial.eval x (roughErrorPolynomial s a0 a) -
      MvPolynomial.eval y (roughErrorPolynomial s a0 a)| ≤
      (s.card : ℝ) * d * A * C ^ d * δ := by
  apply (rough_error_polynomial_oscillation s a0 a x y hA hC hZ hδ ha hx hy hxy).trans
  calc
    ∑ I ∈ s, (∑ j, I j : ℕ) * A * δ * C ^ (∑ j, I j) ≤
        ∑ _I ∈ s, (d : ℝ) * A * δ * C ^ d := by
      apply Finset.sum_le_sum
      intro I hI
      have hd' : ((∑ j, I j : ℕ) : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr (hd I hI)
      have hp : C ^ (∑ j, I j) ≤ C ^ d := pow_le_pow_right₀ hC (hd I hI)
      gcongr
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Hindman168
