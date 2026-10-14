import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Operations

/-! A finite polynomial with constant coefficient one is a genuine unit
when evaluated at a nilpotent element, including the zero-cutoff trivial
ring case. All positive-degree terms commute, as powers of one element. -/

namespace Hindman168
open Finset

variable {𝕜 A : Type*} [CommSemiring 𝕜] [Ring A] [Algebra 𝕜 A]

 theorem nilpotent_smul_pow_of_pos {B : A} (hB : IsNilpotent B)
    (a : 𝕜) {j : ℕ} (hj : 0 < j) : IsNilpotent (a • B ^ j) := by
  obtain ⟨k, hk⟩ := hB
  apply IsNilpotent.smul _ a
  refine ⟨k, ?_⟩
  rw [← pow_mul, Nat.mul_comm j k, pow_mul, hk, zero_pow (Nat.ne_of_gt hj)]

 theorem nilpotent_polynomial_isUnit {B : A} {k : ℕ} (hB : B ^ k = 0)
    (a : ℕ → 𝕜) (ha : a 0 = 1) : IsUnit (∑ j ∈ range k, a j • B ^ j) := by
  cases k with
  | zero =>
    have h1 : (1 : A) = 0 := by simpa only [pow_zero] using hB
    simp only [range_zero, sum_empty]
    rw [← h1]
    exact isUnit_one
  | succ k =>
    have hnil : IsNilpotent (∑ j ∈ range k, a (j + 1) • B ^ (j + 1)) := by
      apply Commute.isNilpotent_sum
      · intro j _
        exact nilpotent_smul_pow_of_pos ⟨k + 1, hB⟩ _ (Nat.succ_pos j)
      · intro i j _ _
        exact (((Commute.refl B).pow_pow (i + 1) (j + 1)).smul_left
          (a (i + 1))).smul_right (a (j + 1))
    have he : (∑ j ∈ range (k + 1), a j • B ^ j) =
        (∑ j ∈ range k, a (j + 1) • B ^ (j + 1)) + 1 := by
      rw [sum_range_succ']
      simp only [ha, pow_zero, one_smul]
    rw [he]
    exact hnil.isUnit_add_one

end Hindman168
