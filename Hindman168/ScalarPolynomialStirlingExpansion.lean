import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

namespace Hindman168
open Polynomial
open scoped BigOperators

/-- The true power-to-falling-factorial identity, with integer Stirling weights. -/
theorem scalar_polynomial_stirling_expansion (n : ℕ) :
    (X : ℝ[X])^n = ∑ i ∈ Finset.range (n+1),
      C (Nat.stirlingSecond n i : ℝ)*descPochhammer ℝ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep (i : ℕ) :
        (X : ℝ[X])*(C (Nat.stirlingSecond n i : ℝ)*descPochhammer ℝ i) =
          C (Nat.stirlingSecond n i : ℝ)*descPochhammer ℝ (i+1) +
            C ((i*Nat.stirlingSecond n i : ℕ) : ℝ)*descPochhammer ℝ i := by
      rw [descPochhammer_succ_right]
      simp only [Nat.cast_mul, map_mul, C_eq_natCast]
      ring
    have hshift :
        (∑ i ∈ Finset.range (n+1),
          C (((i+1)*Nat.stirlingSecond n (i+1) : ℕ) : ℝ)*descPochhammer ℝ (i+1)) =
        ∑ i ∈ Finset.range (n+1),
          C ((i*Nat.stirlingSecond n i : ℕ) : ℝ)*descPochhammer ℝ i := by
      have hz := Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)
      have hh := Finset.sum_range_succ' (fun i =>
        C ((i*Nat.stirlingSecond n i : ℕ) : ℝ)*descPochhammer ℝ i) (n+1)
      rw [Finset.sum_range_succ] at hh
      simpa only [hz, mul_zero, Nat.cast_zero, C_0, zero_mul, zero_add, add_zero] using hh.symm
    have hrec (i : ℕ) :
        C (Nat.stirlingSecond (n+1) (i+1) : ℝ)*descPochhammer ℝ (i+1) =
          C (((i+1)*Nat.stirlingSecond n (i+1) : ℕ) : ℝ)*descPochhammer ℝ (i+1) +
            C (Nat.stirlingSecond n i : ℝ)*descPochhammer ℝ (i+1) := by
      rw [Nat.stirlingSecond_succ_succ, Nat.cast_add, C_add]
      exact add_mul _ _ _
    rw [pow_succ, mul_comm, ih, Finset.mul_sum]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i =>
      C (Nat.stirlingSecond (n+1) i : ℝ)*descPochhammer ℝ i) (n+1)]
    simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, C_0, zero_mul, add_zero, hrec]
    rw [Finset.sum_add_distrib, hshift]
    exact add_comm _ _

end Hindman168
