import Hindman168.RoughDenominatorSubring
import Hindman168.RoughSubringPolynomialDivision

namespace Hindman168
open Polynomial
open scoped BigOperators

theorem rough_cleared_polynomial_coeff_mem (W D k : ℕ) (hD : D ∣ W ^ k)
    (R : ℚ[X]) (P : ℤ[X]) (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ)) :
    ∀ j, R.coeff j ∈ roughDenominatorSubring W := by
  intro j
  apply roughDenominatorSubring_mem_of_dvd W D k hD
  refine ⟨P.coeff j, ?_⟩
  have h := congrArg (fun p : ℚ[X] => p.coeff j) hclear
  rw [coeff_C_mul, coeff_map] at h
  exact h

theorem rough_smooth_quotient_coeff_mem (W D k m l e : ℕ)
    (hD : D ∣ W ^ k) (hm : m ≠ 0) (hmW : m ∣ W ^ l)
    (t : ℤ) (R M : ℚ[X]) (P : ℤ[X])
    (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (hfactor : R = (C (t : ℚ) + C (m : ℚ) * X) ^ e * M) :
    ∀ j, M.coeff j ∈ roughDenominatorSubring W :=
  rough_affine_quotient_coeff_mem (roughDenominatorSubring W) R M t m
    (by exact_mod_cast hm) (intCast_mem (roughDenominatorSubring W) t)
    (roughDenominatorSubring_inverse W m l hm hmW) e
    (rough_cleared_polynomial_coeff_mem W D k hD R P hclear) hfactor

theorem rough_smooth_polynomial_eval (W : ℕ) (M : ℚ[X])
    (hM : ∀ j, M.coeff j ∈ roughDenominatorSubring W) (z : ℤ) :
    M.eval (z : ℚ) ∈ roughDenominatorSubring W := by
  rw [eval_eq_sum_range]
  apply (roughDenominatorSubring W).sum_mem
  intro j _
  exact (roughDenominatorSubring W).mul_mem (hM j)
    ((roughDenominatorSubring W).pow_mem (intCast_mem (roughDenominatorSubring W) z) j)

theorem rough_smooth_quotient_integer_eval (w D k m l e : ℕ)
    (hD : D ∣ (primorial w) ^ k) (hm : m ≠ 0) (hmW : m ∣ (primorial w) ^ l)
    (t z : ℤ) (tau : ℕ) (htau : (tau : ℤ) = t + (m : ℤ) * z)
    (hrough : (primorial w).Coprime tau) (R M : ℚ[X]) (P : ℤ[X])
    (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (hfactor : R = (C (t : ℚ) + C (m : ℚ) * X) ^ e * M)
    (hint : ∃ b : ℤ, R.eval (z : ℚ) = b) : ∃ a : ℤ, M.eval (z : ℚ) = a := by
  apply roughDenominatorSubring_integer_of_rough_power hrough e
    (rough_smooth_polynomial_eval (primorial w) M
      (rough_smooth_quotient_coeff_mem (primorial w) D k m l e hD hm hmW t R M P hclear hfactor) z)
  obtain ⟨b, hb⟩ := hint
  refine ⟨b, ?_⟩
  have hf := congrArg (fun p : ℚ[X] => p.eval (z : ℚ)) hfactor
  simp only [eval_mul, eval_pow, eval_add, eval_C, eval_X] at hf
  have ht : (tau : ℚ) = t + (m : ℚ) * z := by exact_mod_cast htau
  rw [ht]
  exact hf.symm.trans hb

end Hindman168
