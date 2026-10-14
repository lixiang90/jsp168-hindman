import Hindman168.RoughFiniteNewton
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators

namespace Hindman168
open Polynomial
open scoped fwdDiff BigOperators

noncomputable def roughNewtonPolynomial (f : ℕ → ℤ) (q : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (q + 1),
    C (((Δ_[1]^[k] f) 0 : ℚ) / (k.factorial : ℚ)) * descPochhammer ℚ k

theorem roughNewtonPolynomial_degree (f : ℕ → ℤ) (q : ℕ) :
    (roughNewtonPolynomial f q).natDegree ≤ q := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply (natDegree_C_mul_le _ _).trans
  rw [descPochhammer_natDegree]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem roughNewtonPolynomial_eval (f : ℕ → ℤ) (q z : ℕ) :
    (roughNewtonPolynomial f q).eval (z : ℚ) =
      ((∑ k ∈ Finset.range (q + 1), z.choose k • (Δ_[1]^[k] f) 0 : ℤ) : ℚ) := by
  simp only [roughNewtonPolynomial, eval_finsetSum, eval_mul, eval_C, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Nat.cast_mul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

theorem roughNewtonPolynomial_matches (f : ℕ → ℤ) (q H : ℕ)
    (h : ∀ z, z + q + 1 < H → (Δ_[1]^[q + 1] f) z = 0) :
    ∀ z, z < H → (roughNewtonPolynomial f q).eval (z : ℚ) = (f z : ℚ) := by
  intro z hz
  rw [roughNewtonPolynomial_eval, ← rough_finite_newton_formula f q H h z hz]

end Hindman168
