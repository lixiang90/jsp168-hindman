import Hindman168.RoughRationalExactness
import Mathlib.Algebra.Polynomial.DenomsClearable
import Mathlib.Algebra.Polynomial.FieldDivision

namespace Hindman168
open Polynomial

theorem rough_polynomial_ratio_clear (P : ℤ[X]) (q : ℕ) (hP : P.natDegree ≤ q)
    (a : ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ z : ℤ, (m : ℚ) ^ q * (P.map (Int.castRingHom ℚ)).eval ((a : ℚ) / m) = z := by
  have hmn : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨z, bi, hbi, hz⟩ := denomsClearable_of_natDegree_le
    (i := Int.castRingHom ℚ) (b := (m : ℤ)) (bi := (m : ℚ)⁻¹) q a
    (by change (m : ℚ)⁻¹ * ((m : ℤ) : ℚ) = 1
        simpa only [Int.cast_natCast] using inv_mul_cancel₀ hmn) P hP
  change bi * ((m : ℤ) : ℚ) = 1 at hbi
  change (z : ℚ) = ((m : ℤ) : ℚ) ^ q *
    (P.map (Int.castRingHom ℚ)).eval ((a : ℚ) * bi) at hz
  have hb : bi = (m : ℚ)⁻¹ := by
    apply (mul_right_cancel₀ hmn)
    simpa only [Int.cast_natCast, inv_mul_cancel₀ hmn] using hbi
  refine ⟨z, ?_⟩
  simpa only [hb, Int.cast_natCast, div_eq_mul_inv] using hz.symm

theorem rough_polynomial_derivative_clear (R : ℚ[X]) (P : ℤ[X]) (D q : ℕ)
    (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ)) (hP : P.natDegree ≤ q)
    (a : ℤ) (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ∃ z : ℤ, ((D * m ^ q : ℕ) : ℚ) *
      (derivative^[j] R).eval ((a : ℚ) / m) = z := by
  have hdeg : (derivative^[j] P).natDegree ≤ q :=
    (natDegree_iterate_derivative P j).trans ((Nat.sub_le _ _).trans hP)
  obtain ⟨z, hz⟩ := rough_polynomial_ratio_clear (derivative^[j] P) q hdeg a m hm
  have h := congrArg (fun Q : ℚ[X] => derivative^[j] Q) hclear
  rw [iterate_derivative_C_mul, iterate_derivative_map] at h
  rw [← h, eval_mul, eval_C] at hz
  refine ⟨z, ?_⟩
  push_cast
  linear_combination hz

theorem rough_polynomial_small_derivative_zero (R : ℚ[X]) (P : ℤ[X]) (D q : ℕ)
    (hD : 0 < D) (hclear : C (D : ℚ) * R = P.map (Int.castRingHom ℚ))
    (hP : P.natDegree ≤ q) (a : ℤ) (m : ℕ) (hm : 0 < m) (j : ℕ)
    (hsmall : |(((derivative^[j] R).eval ((a : ℚ) / m) : ℚ) : ℝ)| <
      1 / ((D : ℝ) * (m : ℝ) ^ q)) :
    (derivative^[j] R).eval ((a : ℚ) / m) = 0 := by
  obtain ⟨z, hz⟩ := rough_polynomial_derivative_clear R P D q hclear hP a m hm j
  have hzR := congrArg (fun r : ℚ => (r : ℝ)) hz
  have hzero := rough_lattice_eq_zero (Nat.mul_pos hD (pow_pos hm q))
    (x := (((derivative^[j] R).eval ((a : ℚ) / m) : ℚ) : ℝ))
    ⟨z, by exact_mod_cast hzR⟩ (by simpa only [Nat.cast_mul, Nat.cast_pow] using hsmall)
  exact_mod_cast hzero

end Hindman168
