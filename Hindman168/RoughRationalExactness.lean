import Hindman168.RoughDenominatorUnits
import Mathlib.Data.Rat.Cast.Order

namespace Hindman168

theorem rough_integer_eq_zero_of_abs_lt_one {a : ℤ} (h : |(a : ℝ)| < 1) : a = 0 := by
  have ha : |a| < (1 : ℤ) := by exact_mod_cast h
  have := abs_lt.mp ha
  omega

theorem rough_lattice_eq_zero {D : ℕ} (hD : 0 < D) {x : ℝ}
    (hx : ∃ a : ℤ, (D : ℝ) * x = a) (hsmall : |x| < 1 / (D : ℝ)) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hz : a = 0 := rough_integer_eq_zero_of_abs_lt_one (by
    rw [← ha, abs_mul, abs_of_pos hd]
    have h := (lt_div_iff₀ hd).mp hsmall
    simpa only [mul_comm] using h)
  rw [hz, Int.cast_zero] at ha
  exact (mul_eq_zero.mp ha).resolve_left hd.ne'

theorem rough_lattice_near_integer {D : ℕ} (hD : 0 < D) {x : ℝ}
    (hx : ∃ a : ℤ, (D : ℝ) * x = a) (k : ℤ)
    (hsmall : |x - k| < 1 / (D : ℝ)) : x = k := by
  apply sub_eq_zero.mp
  apply rough_lattice_eq_zero hD _ hsmall
  obtain ⟨a, ha⟩ := hx
  refine ⟨a - (D : ℤ) * k, ?_⟩
  push_cast
  rw [mul_sub, ha]

theorem rough_coprime_integer_cancel {D t : ℕ} (hDt : D.Coprime t) {x : ℚ}
    (hD : ∃ a : ℤ, (D : ℚ) * x = a) (ht : ∃ b : ℤ, (t : ℚ) * x = b) :
    ∃ k : ℤ, x = k := by
  obtain ⟨a, ha⟩ := hD
  obtain ⟨b, hb⟩ := ht
  have hbez : (1 : ℚ) = (D : ℚ) * (Nat.gcdA D t : ℚ) + t * (Nat.gcdB D t : ℚ) := by
    exact_mod_cast (hDt.gcd_eq_one ▸ Nat.gcd_eq_gcd_ab D t)
  refine ⟨a * Nat.gcdA D t + b * Nat.gcdB D t, ?_⟩
  push_cast
  rw [← ha, ← hb]
  linear_combination x * hbez

theorem rough_smooth_denominator_integer_cancel {D t w : ℕ} (k e : ℕ)
    (hD : D ∣ (primorial w) ^ k) (ht : (primorial w).Coprime t) {x : ℚ}
    (hx : ∃ a : ℤ, (D : ℚ) * x = a)
    (hpower : ∃ b : ℤ, (t : ℚ) ^ e * x = b) : ∃ a : ℤ, x = a := by
  apply rough_coprime_integer_cancel ((smooth_denominator_coprime k hD ht).pow_right e) hx
  simpa only [Nat.cast_pow] using hpower

end Hindman168
