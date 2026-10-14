import Hindman168.RoughPolynomialDenominators
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Rat
import Mathlib.LinearAlgebra.Lagrange

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem rough_rational_polynomial_clear (R : ℚ[X]) :
    ∃ D : ℕ, 0 < D ∧ ∃ P : ℤ[X], C (D : ℚ) * R = P.map (Int.castRingHom ℚ) := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) R
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) R
  have hp : P.map (Int.castRingHom ℚ) = C (b : ℚ) * R := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from Subsingleton.elim _ _]
    simpa only [P, ← smul_eq_C_mul, Int.cast_smul_eq_zsmul] using h
  refine ⟨b.natAbs ^ 2, pow_pos (Int.natAbs_pos.mpr hb0) 2, C b * P, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, hp]
  change C ((b.natAbs ^ 2 : ℕ) : ℚ) * R = C (b : ℚ) * (C (b : ℚ) * R)
  have hc : ((b.natAbs ^ 2 : ℕ) : ℚ) = (b : ℚ) * b := by
    have hi : (b.natAbs : ℤ) ^ 2 = b * b := by
      rw [Int.natCast_natAbs, sq_abs, pow_two]
    have hr := congrArg (fun z : ℤ => (z : ℚ)) hi
    simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_mul, Nat.cast_pow] using hr
  rw [hc, map_mul, mul_assoc]

theorem rough_finite_polynomial_common_denominator {ι : Type*} [Fintype ι]
    (R : ι → ℚ[X]) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ P : ℤ[X], C (D : ℚ) * R i = P.map (Int.castRingHom ℚ) := by
  choose d hd P hP using fun i => rough_rational_polynomial_clear (R i)
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => hd i), ?_⟩
  intro i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  refine ⟨C (c : ℤ) * P i, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, ← hP, hc]
  change C ((d i * c : ℕ) : ℚ) * R i = C ((c : ℤ) : ℚ) * (C (d i : ℚ) * R i)
  push_cast
  rw [map_mul]
  ring

theorem rough_interpolation_fixed_denominator {ι : Type*} [Fintype ι]
    (nodes : ι → ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∀ values : ι → ℤ, ∃ P : ℤ[X],
      C (D : ℚ) * Lagrange.interpolate Finset.univ (fun i => (nodes i : ℚ))
        (fun i => (values i : ℚ)) = P.map (Int.castRingHom ℚ) := by
  obtain ⟨D, hD, h⟩ := rough_finite_polynomial_common_denominator
    (fun i => Lagrange.basis Finset.univ (fun j => (nodes j : ℚ)) i)
  choose P hP using h
  refine ⟨D, hD, fun values => ⟨∑ i, C (values i) * P i, ?_⟩⟩
  rw [Lagrange.interpolate_apply, Finset.mul_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_C, ← hP]
  change C (D : ℚ) * (C (values i : ℚ) * _) = C (values i : ℚ) * (C (D : ℚ) * _)
  ring

end Hindman168
