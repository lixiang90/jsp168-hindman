import Hindman168.FiniteComplexSetMean

/-! Transfer bounds from a genuine retained length to the original scale.
The coefficient degree and the retained proportion are explicit. -/
namespace Hindman168

theorem finite_coefficient_scale_transfer (N M : ℕ) (τ A x : ℝ) (d j : ℕ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hA : 0 ≤ A) (hx : 0 ≤ x)
    (hlen : τ*(N : ℝ) ≤ M) (hj : j ≤ d) (hbound : (M : ℝ)^j*x ≤ A) :
    (N : ℝ)^j*x ≤ A*(τ⁻¹)^d := by
  have hN : (N : ℝ) ≤ τ⁻¹*(M : ℝ) := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hlen)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg N) hN j
  have hInv : 1 ≤ τ⁻¹ := (one_le_inv₀ hτ).mpr hτ1
  calc
    _ ≤ (τ⁻¹*(M : ℝ))^j*x := mul_le_mul_of_nonneg_right hpow hx
    _ = (τ⁻¹)^j*((M : ℝ)^j*x) := by rw [mul_pow]; ring
    _ ≤ (τ⁻¹)^j*A := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (τ⁻¹)^d*A := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hInv hj) hA
    _ = _ := mul_comm _ _

end Hindman168
