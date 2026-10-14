import Hindman168.ScalarPolynomialIntegerCoefficientRecovery
import Mathlib.Data.Nat.Choose.Bounds

namespace Hindman168

theorem scalar_progression_recovery_weight_abs (a q D i j : ℕ) :
    |(scalarProgressionRecoveryWeight a q D i j : ℝ)| =
      (q : ℝ)^(D-j)*(j.choose i : ℝ)*(a : ℝ)^(j-i) := by
  simp only [scalarProgressionRecoveryWeight, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_neg, abs_mul, abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) a), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (j.choose i))]

theorem scalar_progression_recovery_weight_bound (a q D i j N : ℕ)
    (hq : 0 < q) (ha : a ≤ N) (hj : j ≤ D) :
    |(scalarProgressionRecoveryWeight a q D i j : ℝ)| ≤
      (q : ℝ)^D*(2 : ℝ)^D*(N : ℝ)^(j-i) := by
  rw [scalar_progression_recovery_weight_abs]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow := pow_le_pow_right₀ hq1 (Nat.sub_le D j)
  have hchoose : (j.choose i : ℝ) ≤ (2 : ℝ)^D := by
    have hh := (Nat.choose_le_two_pow j i).trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hj)
    exact_mod_cast hh
  have hpowA : (a : ℝ)^(j-i) ≤ (N : ℝ)^(j-i) :=
    pow_le_pow_left₀ (Nat.cast_nonneg a) (by exact_mod_cast ha) _
  exact mul_le_mul (mul_le_mul hpow hchoose (Nat.cast_nonneg _) (by positivity))
    hpowA (by positivity) (by positivity)

end Hindman168
