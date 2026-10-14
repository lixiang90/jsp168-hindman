import Hindman168.RoughRationalInterpolationError
import Hindman168.RoughInterpolationValueError

namespace Hindman168
open Polynomial

theorem rough_interpolation_progression_geometry {H t m : ℕ} {S : ℝ}
    (hH : 2 ≤ H) (hm : 0 < m)
    (hprog : ∀ z : ℕ, z < H → S ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S) :
    (m : ℝ) ≤ S ∧ |(-(t : ℝ) / m)| ≤ 2 * S := by
  have h0 := hprog 0 (by omega)
  have h1 := hprog 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.cast_add] at h0 h1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨by linarith, ?_⟩
  rw [abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg t), abs_of_pos hmp]
  exact (div_le_self (Nat.cast_nonneg t) hm1).trans h0.2.le

theorem rough_affine_power_derivatives_zero (theta : ℝ[X]) (t m : ℝ) (hm : m ≠ 0)
    (e j : ℕ) (hj : j < e) :
    (derivative^[j] ((C t + C m * X) ^ e * theta)).eval (-t / m) = 0 := by
  have hd := pow_sub_dvd_iterate_derivative_of_pow_dvd (R := ℝ) j
    (show (C t + C m * X) ^ e ∣ (C t + C m * X) ^ e * theta from dvd_mul_right _ _)
  obtain ⟨Q, hQ⟩ := hd
  rw [hQ, eval_mul, eval_pow, eval_add, eval_C, eval_mul, eval_C, eval_X]
  have hz : t + m * (-t / m) = 0 := by field_simp; ring
  rw [hz, zero_pow (Nat.sub_ne_zero_of_lt hj), zero_mul]

theorem rough_interpolation_choose_integer_data {q H : ℕ} (hH : 0 < H)
    (T : ℝ[X]) (eps : ℝ)
    (hnear : ∀ z : ℕ, z < H → ∃ b : ℤ, |T.eval (z : ℝ) - b| ≤ eps) :
    ∃ values : Fin (q + 1) → ℤ,
      ∀ i, |(values i : ℝ) - T.eval (roughInterpolationNode q H i : ℝ)| ≤ eps := by
  have h (i : Fin (q + 1)) := hnear (roughInterpolationNode q H i) (roughInterpolationNode_bounds hH i)
  choose values hv using h
  exact ⟨values, fun i => by simpa only [abs_sub_comm] using hv i⟩

end Hindman168
