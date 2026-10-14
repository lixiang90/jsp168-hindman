import Hindman168.RoughPolynomialDenominators

namespace Hindman168
open Polynomial

theorem rough_root_power_dvd (R : ℚ[X]) (a : ℚ) (e : ℕ)
    (hzero : ∀ j < e, (derivative^[j] R).eval a = 0) : (X - C a) ^ e ∣ R := by
  by_cases hR : R = 0
  · rw [hR]
    exact dvd_zero _
  by_cases he : e = 0
  · simp only [he, pow_zero, one_dvd]
  apply (le_rootMultiplicity_iff hR).mp
  have h := lt_rootMultiplicity_of_isRoot_iterate_derivative hR
    (n := e - 1) (t := a) (fun j hj => hzero j (by omega))
  omega

theorem rough_affine_exact_division (R : ℚ[X]) (t m : ℚ) (hm : m ≠ 0) (e q : ℕ)
    (hdeg : R.natDegree ≤ q)
    (hzero : ∀ j < e, (derivative^[j] R).eval (-t / m) = 0) :
    ∃ M : ℚ[X], R = (C t + C m * X) ^ e * M ∧ M.natDegree ≤ q - e := by
  by_cases hR : R = 0
  · refine ⟨0, by simp only [hR, mul_zero], ?_⟩
    simp only [natDegree_zero, zero_le]
  obtain ⟨Q, hQ⟩ := rough_root_power_dvd R (-t / m) e hzero
  have hQne : Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hQ
    exact hR hQ
  have ha : C t + C m * X = C m * (X - C (-t / m)) := by
    rw [mul_sub, ← C_mul]
    have h : m * (-t / m) = -t := by field_simp
    rw [h, map_neg]
    ring
  have hbound : Q.natDegree ≤ q - e := by
    have hd := hdeg
    rw [hQ, natDegree_mul (pow_ne_zero e (X_sub_C_ne_zero _)) hQne,
      natDegree_pow, natDegree_X_sub_C, mul_one] at hd
    omega
  refine ⟨C ((m⁻¹) ^ e) * Q, ?_, ?_⟩
  · rw [ha, mul_pow, ← C_pow]
    have hc : C (m ^ e) * C ((m⁻¹) ^ e) = (1 : ℚ[X]) := by
      rw [← C_mul, ← mul_pow, mul_inv_cancel₀ hm, one_pow, map_one]
    calc
      R = (X - C (-t / m)) ^ e * Q := hQ
      _ = (C (m ^ e) * C ((m⁻¹) ^ e)) * ((X - C (-t / m)) ^ e * Q) := by rw [hc, one_mul]
      _ = _ := by ring
  · rw [natDegree_C_mul (pow_ne_zero e (inv_ne_zero hm))]
    exact hbound

theorem rough_small_derivatives_exact_division (R : ℚ[X]) (P : ℤ[X])
    (D q e : ℕ) (hD : 0 < D)
    (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (hP : P.natDegree ≤ q) (hR : R.natDegree ≤ q) (t : ℤ) (m : ℕ) (hm : 0 < m)
    (hsmall : ∀ j < e,
      |(((derivative^[j] R).eval (-(t : ℚ) / m) : ℚ) : ℝ)| <
        1 / ((D : ℝ) * (m : ℝ) ^ q)) :
    ∃ M : ℚ[X], R = (C (t : ℚ) + C (m : ℚ) * X) ^ e * M ∧
      M.natDegree ≤ q - e := by
  apply rough_affine_exact_division R t m (by exact_mod_cast hm.ne') e q hR
  intro j hj
  simpa only [Int.cast_neg] using rough_polynomial_small_derivative_zero R P D q hD
    hclear hP (-t) m hm j (by simpa only [Int.cast_neg] using hsmall j hj)

end Hindman168
