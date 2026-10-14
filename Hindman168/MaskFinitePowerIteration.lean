import Hindman168.MaskFiniteElimination

/-! Finite powered mask iteration with an explicit vanishing error.
Squaring the sum of main term and error retains both with a factor two;
no bound on an intermediate correlation is needed. -/

namespace Hindman168
open Filter
open scoped Topology

noncomputable def maskPowerCoefficient (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => 2 * c * maskPowerCoefficient c k ^ 2

noncomputable def maskPowerError (c : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => 2 * maskPowerCoefficient c k ^ 2 * e k + 2 * maskPowerError c e k ^ 2

theorem maskPowerCoefficient_nonneg {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    0 ≤ maskPowerCoefficient c k := by
  cases k with
  | zero => simp [maskPowerCoefficient]
  | succ k => dsimp [maskPowerCoefficient]; positivity

theorem maskPowerCoefficient_ge_one {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    1 ≤ maskPowerCoefficient c k := by
  induction k with
  | zero => simp [maskPowerCoefficient]
  | succ k ih =>
    have hs : 1 ≤ maskPowerCoefficient c k ^ 2 := by nlinarith
    dsimp only [maskPowerCoefficient]
    nlinarith

theorem maskPowerError_nonneg (c : ℝ) (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k) (k : ℕ) :
    0 ≤ maskPowerError c e k := by
  cases k with
  | zero => simp [maskPowerError]
  | succ k =>
    have hk := he k
    dsimp [maskPowerError]
    positivity

theorem maskPowerError_tendsto_zero (c : ℝ) (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Tendsto (e k) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun w => maskPowerError c (fun j => e j w) k) atTop (𝓝 0) := by
  induction k with
  | zero => exact tendsto_const_nhds
  | succ k ih =>
    have ht := ((he k).const_mul (2 * maskPowerCoefficient c k ^ 2)).add ((ih.pow 2).const_mul 2)
    simpa only [maskPowerError, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using ht

theorem finite_mask_power_iteration (c : ℝ) (e x : ℕ → ℝ) (L : ℕ) (hx : ∀ k ≤ L, 0 ≤ x k)
    (hs : ∀ k < L, x k ^ 2 ≤ c * x (k+1) + e k) :
    ∀ k ≤ L, x 0 ^ (2 ^ k) ≤ maskPowerCoefficient c k * x k + maskPowerError c e k := by
  intro k
  induction k with
  | zero => intro _; simp [maskPowerCoefficient, maskPowerError]
  | succ k ih =>
    intro hk
    have hkL : k ≤ L := by omega
    have hb := ih hkL
    calc
      x 0 ^ (2 ^ (k+1)) = (x 0 ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (maskPowerCoefficient c k * x k + maskPowerError c e k) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (hx 0 (Nat.zero_le L)) _) hb 2
      _ ≤ 2 * maskPowerCoefficient c k ^ 2 * x k ^ 2 + 2 * maskPowerError c e k ^ 2 := by
        nlinarith [sq_nonneg (maskPowerCoefficient c k * x k - maskPowerError c e k)]
      _ ≤ 2 * maskPowerCoefficient c k ^ 2 * (c * x (k+1) + e k) + 2 * maskPowerError c e k ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (hs k (by omega))
          (show 0 ≤ 2 * maskPowerCoefficient c k ^ 2 from by positivity)) le_rfl
      _ = maskPowerCoefficient c (k+1) * x (k+1) + maskPowerError c e (k+1) := by
        dsimp only [maskPowerCoefficient, maskPowerError]
        ring

theorem nonnegative_add_pow_le_double (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    (u+v) ^ n ≤ 2 ^ n * u ^ n + 2 ^ n * v ^ n := by
  by_cases h : u ≤ v
  · calc
      _ ≤ (2*v)^n := pow_le_pow_left₀ (add_nonneg hu hv) (by linarith) n
      _ = 2^n * v^n := mul_pow _ _ _
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · calc
      _ ≤ (2*u)^n := pow_le_pow_left₀ (add_nonneg hu hv) (by linarith) n
      _ = 2^n * u^n := mul_pow _ _ _
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

end Hindman168
