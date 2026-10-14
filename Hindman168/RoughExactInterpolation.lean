import Hindman168.RoughInterpolationProgression

namespace Hindman168
open Polynomial Filter
open scoped Topology

theorem rough_exact_interpolation_eventually
    {α : Type*} {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (e q H : ℕ) (he : 0 < e) (heq : e ≤ q) (hH : 2 * q + 2 ≤ H)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : ℝ[X]), 0 < m →
      (∀ p, p.Prime → p ∣ m → p ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t + m * z)) →
      ((C (t : ℝ) + C (m : ℝ) * X) ^ e * theta).natDegree ≤ q →
      (∀ z : ℕ, z < H → ∃ b : ℤ,
        |((C (t : ℝ) + C (m : ℝ) * X) ^ e * theta).eval (z : ℝ) - (b : ℝ)| ≤
          A * (S w / Z w) ^ e) →
      ∃ M : ℚ[X], M.natDegree ≤ q - e ∧
        (∀ j p, p.Prime → p ∣ (M.coeff j).den → p ≤ W w) ∧
        ∀ z : ℕ, z < H → (∃ b : ℤ, M.eval (z : ℚ) = b) ∧
          |theta.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ)| ≤
            roughInterpolationConstant q * A * (Z w)⁻¹ ^ e := by
  have hq : 0 < q := he.trans_le heq
  obtain ⟨D, hD, hmodel⟩ := roughRationalInterpolation_fixed_integer_model hq hH
  have hc := roughInterpolationConstant_pos q
  have hz0 := hZ.mono (fun _ h => h.le)
  have hdiv := rough_interpolation_exact_division_eventually hg hS hz0 D q e hD he
    (roughInterpolationConstant q * A) (mul_pos hc hA).le
  have hint := rough_interpolation_error_eventually hg hS hz0
    ((roughInterpolationConstant q + 1) * A) (by positivity) D (by exact_mod_cast hD) 0 e he
  filter_upwards [hdiv, hint, hW.eventually (eventually_ge_atTop D), hS, hZ] with w hd hi hDw hs hz
  intro t m theta hm hmsmooth hprog hrough hdeg hnear
  let T : ℝ[X] := (C (t : ℝ) + C (m : ℝ) * X) ^ e * theta
  let eps : ℝ := A * (S w / Z w) ^ e
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hgeom := rough_interpolation_progression_geometry (by omega : 2 ≤ H) hm hprog
  obtain ⟨values, hv⟩ := rough_interpolation_choose_integer_data (by omega : 0 < H) T eps hnear
  let R := roughRationalInterpolation q H values
  obtain ⟨P, hclear, hP⟩ := hmodel values
  have hR := roughRationalInterpolation_degree hq hH values
  have hder : ∀ j < e, |(((derivative^[j] R).eval (-((t : ℤ) : ℚ) / m) : ℚ) : ℝ)| ≤
      (roughInterpolationConstant q * A) * (S w / Z w) ^ e * (1 + 2 * S w) ^ q := by
    intro j hj
    have hb := rough_rational_interpolation_derivative_error hq hH T hdeg values eps heps hv
      j (by omega) (S w) (-(t : ℚ) / m) (by linarith)
      (by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_natCast] using hgeom.2)
    have hzero := rough_affine_power_derivatives_zero theta (t : ℝ) (m : ℝ)
      (by exact_mod_cast hm.ne') e j hj
    dsimp only [T] at hb
    simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_natCast] at hb
    rw [hzero, sub_zero] at hb
    simpa only [R, eps, Int.cast_natCast, mul_assoc] using hb
  obtain ⟨M, hfactor, hM⟩ := hd R P (t : ℤ) m hm hgeom.1 hclear hP hR hder
  refine ⟨M, hM, ?_, ?_⟩
  · exact rough_smooth_quotient_prime_support hD.ne' hDw hm.ne' hmsmooth e
      (t : ℤ) R M P hclear hfactor
  · intro z hzH
    have hb := rough_rational_interpolation_value_error hq hH T hdeg values eps heps hv
      (z : ℚ) (by positivity) (by exact_mod_cast (show z ≤ H - 1 by omega))
    have hb' : |((R.eval (z : ℚ) : ℚ) : ℝ) - T.eval (z : ℝ)| ≤ roughInterpolationConstant q * eps := by
      simpa only [R, Rat.cast_natCast] using hb
    obtain ⟨b, hbint⟩ := hnear z hzH
    have hrnear := rough_interpolation_near_integer_bound hb' hbint
    have hsmall : |((R.eval (z : ℚ) : ℚ) : ℝ) - (b : ℝ)| < 1 / (D : ℝ) := by
      apply hrnear.trans_lt
      simpa only [eps, pow_zero, mul_one, mul_assoc] using hi
    have hRinteger : R.eval ((z : ℤ) : ℚ) = (b : ℚ) :=
      rough_cleared_polynomial_near_integer R P D hD hclear (z : ℤ) b
        (by simpa only [Int.cast_natCast] using hsmall)
    have hinteger := rough_smooth_quotient_integer_eval (W w) D (W w) m m e
      (fixed_integer_dvd_primorial_power hD.ne' hDw) hm.ne'
      (rough_smooth_integer_dvd_primorial_power hm.ne' hmsmooth)
      (t : ℤ) (z : ℤ) (t + m * z) (by push_cast; rfl) (hrough z hzH)
      R M P hclear hfactor ⟨b, hRinteger⟩
    refine ⟨by simpa only [Int.cast_natCast] using hinteger, ?_⟩
    have hf := congrArg (fun Q : ℚ[X] => Q.eval (z : ℚ)) hfactor
    simp only [eval_mul, eval_pow, eval_add, eval_C, eval_X, Int.cast_natCast] at hf
    have hfR := congrArg (fun x : ℚ => (x : ℝ)) hf
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast] at hfR
    have htarget : T.eval (z : ℝ) = ((t + m * z : ℕ) : ℝ) ^ e * theta.eval (z : ℝ) := by
      simp only [T, eval_mul, eval_pow, eval_add, eval_C, eval_X, Nat.cast_add, Nat.cast_mul]
    have hfac : ((R.eval (z : ℚ) : ℚ) : ℝ) =
        ((t + m * z : ℕ) : ℝ) ^ e * ((M.eval (z : ℚ) : ℚ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hfR
    have herr : |((t + m * z : ℕ) : ℝ) ^ e * theta.eval (z : ℝ) -
        ((R.eval (z : ℚ) : ℚ) : ℝ)| ≤ (roughInterpolationConstant q * A) * (S w / Z w) ^ e := by
      rw [← htarget, abs_sub_comm]
      simpa only [eps, mul_assoc] using hb'
    exact rough_interpolation_divided_error (by linarith) (hprog z hzH).1 e hfac herr

end Hindman168
