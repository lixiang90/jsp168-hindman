import Hindman168.RoughNewtonPolynomial
import Mathlib.Data.Rat.Lemmas

namespace Hindman168
open Polynomial
open scoped fwdDiff BigOperators

theorem rough_rat_den_dvd_of_integer_mul (D : ℕ) (hD : D ≠ 0) (x : ℚ)
    (hx : ∃ a : ℤ, (D : ℚ) * x = (a : ℚ)) : x.den ∣ D := by
  obtain ⟨a, ha⟩ := hx
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have he : x = Rat.divInt a (D : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using ha
  have h := Rat.den_dvd a (D : ℤ)
  rw [← he] at h
  exact_mod_cast h

theorem roughNewtonPolynomial_coeff_clear (f : ℕ → ℤ) (q j : ℕ) :
    ∃ a : ℤ, (q.factorial : ℚ) * (roughNewtonPolynomial f q).coeff j = (a : ℚ) := by
  refine ⟨∑ k ∈ Finset.range (q + 1),
    ((q.factorial / k.factorial : ℕ) : ℤ) * (Δ_[1]^[k] f) 0 * (descPochhammer ℤ k).coeff j, ?_⟩
  simp only [roughNewtonPolynomial, finsetSum_coeff, coeff_C_mul, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hdiv := Nat.factorial_dvd_factorial (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hfact : (q.factorial : ℚ) = ((q.factorial / k.factorial : ℕ) : ℚ) * (k.factorial : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel hdiv).symm
  have hk0 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [← descPochhammer_map (Int.castRingHom ℚ) k, coeff_map]
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hfact]
  field_simp
  rfl

theorem roughNewtonPolynomial_den_dvd (f : ℕ → ℤ) (q j : ℕ) :
    ((roughNewtonPolynomial f q).coeff j).den ∣ q.factorial :=
  rough_rat_den_dvd_of_integer_mul q.factorial q.factorial_ne_zero _
    (roughNewtonPolynomial_coeff_clear f q j)

end Hindman168
