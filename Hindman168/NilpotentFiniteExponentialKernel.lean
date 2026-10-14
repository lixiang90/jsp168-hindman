import Hindman168.NilpotentPolynomialUnit

/-! If a finite exponential series of a nilpotent element equals one,
the element is zero. The proof factors the actual series minus one by
the element and a genuine constant-one polynomial unit. -/

namespace Hindman168
open Finset

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

 theorem nilpotent_finite_exponential_factor {B : A} {k : ℕ} (hB : B ^ k = 0) :
    B * (∑ j ∈ range k, ((j + 1).factorial : 𝕜)⁻¹ • B ^ j) + 1 =
      ∑ j ∈ range k, (j.factorial : 𝕜)⁻¹ • B ^ j := by
  have hm : B * (∑ j ∈ range k, ((j + 1).factorial : 𝕜)⁻¹ • B ^ j) =
      ∑ j ∈ range k, ((j + 1).factorial : 𝕜)⁻¹ • B ^ (j + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [mul_smul_comm, ← pow_succ']
  rw [hm]
  calc
    _ = ∑ j ∈ range (k + 1), (j.factorial : 𝕜)⁻¹ • B ^ j := by
      rw [sum_range_succ']
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    _ = _ := by
      rw [sum_range_succ, hB, smul_zero, add_zero]

 theorem eq_zero_of_nilpotent_finite_exponential_eq_one {B : A} {k : ℕ}
    (hB : B ^ k = 0) (h : (∑ j ∈ range k, (j.factorial : 𝕜)⁻¹ • B ^ j) = 1) : B = 0 := by
  let Q : A := ∑ j ∈ range k, ((j + 1).factorial : 𝕜)⁻¹ • B ^ j
  have hQ : IsUnit Q := by
    apply nilpotent_polynomial_isUnit hB
    simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one]
  have hf : B * Q + 1 = 1 := (nilpotent_finite_exponential_factor hB).trans h
  have he : B * Q = 0 := add_right_cancel (by simpa only [zero_add] using hf)
  exact hQ.mul_left_eq_zero.mp he

end Hindman168
