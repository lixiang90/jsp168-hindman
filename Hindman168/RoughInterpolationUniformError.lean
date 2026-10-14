import Hindman168.RoughScaledInterpolation

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def roughInterpolationConstant (q : ℕ) : ℝ :=
  roughFixedInterpolationMass q * (1 + 2 * q) ^ q

theorem roughInterpolationConstant_pos (q : ℕ) : 0 < roughInterpolationConstant q := by
  exact mul_pos (roughFixedInterpolationMass_pos q) (by positivity)

theorem roughInterpolationConstant_mass_le (q : ℕ) :
    roughFixedInterpolationMass q ≤ roughInterpolationConstant q := by
  apply le_mul_of_one_le_right (roughFixedInterpolationMass_pos q).le
  exact one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) q])

theorem roughScaledInterpolation_error_identity (q : ℕ) (h : ℝ) (hh : h ≠ 0)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (values : Fin (q + 1) → ℝ) :
    roughScaledInterpolation q h values - T = roughScaledInterpolation q h
      (fun i => values i - T.eval ((i.val : ℝ) * h)) := by
  have hs := roughScaledInterpolation_sub q h values (fun i => T.eval ((i.val : ℝ) * h))
  rw [roughScaledInterpolation_reproduce q h hh T hT] at hs
  exact hs.symm

theorem roughScaledInterpolation_error_derivative_bound (q j : ℕ) (hj : j ≤ q)
    (h : ℝ) (hh : 1 ≤ h) (T : ℝ[X]) (hT : T.natDegree ≤ q)
    (values : Fin (q + 1) → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i, |values i - T.eval ((i.val : ℝ) * h)| ≤ eps)
    (B x : ℝ) (hB : 1 ≤ B) (hx : |x / h| ≤ B) :
    |(derivative^[j] (roughScaledInterpolation q h values - T)).eval x| ≤
      eps * roughFixedInterpolationMass q * B ^ q := by
  rw [roughScaledInterpolation_error_identity q h (by linarith) T hT values]
  exact roughScaledInterpolation_derivative_bound q j hj h hh _ eps heps herr B x hB hx

theorem rough_interpolation_uniform_value_error {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (values : Fin (q + 1) → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i, |values i - T.eval (roughInterpolationNode q H i : ℝ)| ≤ eps)
    (z : ℝ) (hz : 0 ≤ z) (hzH : z ≤ ((H - 1 : ℕ) : ℝ)) :
    |(roughScaledInterpolation q (roughInterpolationStep q H) values).eval z - T.eval z| ≤
      roughInterpolationConstant q * eps := by
  have hh : (1 : ℝ) ≤ roughInterpolationStep q H := by
    exact_mod_cast roughInterpolationStep_pos hq hH
  have hscaled := roughInterpolationStep_scaled_interval hq hH hz hzH
  have hv : ∀ i : Fin (q + 1), |values i - T.eval ((i.val : ℝ) * roughInterpolationStep q H)| ≤ eps := by
    simpa only [roughInterpolationNode, Nat.cast_mul] using herr
  have hb := roughScaledInterpolation_error_derivative_bound q 0 (by omega)
    (roughInterpolationStep q H) hh T hT values eps heps hv
    (1 + 2 * q) z (by linarith [Nat.cast_nonneg (α := ℝ) q])
    (by rw [abs_of_nonneg hscaled.1]; linarith [hscaled.2])
  simpa only [Function.iterate_zero_apply, eval_sub, roughInterpolationConstant,
    mul_assoc, mul_comm, mul_left_comm] using hb

theorem rough_interpolation_uniform_derivative_error {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (T : ℝ[X]) (hT : T.natDegree ≤ q) (values : Fin (q + 1) → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ i, |values i - T.eval (roughInterpolationNode q H i : ℝ)| ≤ eps)
    (j : ℕ) (hj : j ≤ q) (S a : ℝ) (hS : 0 ≤ S) (ha : |a| ≤ 2 * S) :
    |(derivative^[j] (roughScaledInterpolation q (roughInterpolationStep q H) values - T)).eval a| ≤
      roughInterpolationConstant q * eps * (1 + 2 * S) ^ q := by
  have hh : (1 : ℝ) ≤ roughInterpolationStep q H := by
    exact_mod_cast roughInterpolationStep_pos hq hH
  have hp : (0 : ℝ) < roughInterpolationStep q H := by linarith
  have hv : ∀ i : Fin (q + 1), |values i - T.eval ((i.val : ℝ) * roughInterpolationStep q H)| ≤ eps := by
    simpa only [roughInterpolationNode, Nat.cast_mul] using herr
  have hx : |a / roughInterpolationStep q H| ≤ 1 + 2 * S := by
    rw [abs_div, abs_of_pos hp]
    have hd := div_le_self (abs_nonneg a) hh
    linarith
  have hb := roughScaledInterpolation_error_derivative_bound q j hj
    (roughInterpolationStep q H) hh T hT values eps heps hv (1 + 2 * S) a (by linarith) hx
  apply hb.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (roughInterpolationConstant_mass_le q) heps)
    (pow_nonneg (by linarith : 0 ≤ 1 + 2 * S) q)
  simpa only [mul_comm eps] using h

end Hindman168
