import Hindman168.RoughDescentModels

namespace Hindman168
open Polynomial

theorem rough_affine_comp_degree {R : Type*} [Semiring R]
    (P : R[X]) (a b : R) : (P.comp (C a + C b * X)).natDegree ≤ P.natDegree := by
  have hlin : (C a + C b * X : R[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le)
  exact natDegree_comp_le.trans (by simpa only [mul_one] using Nat.mul_le_mul_left P.natDegree hlin)

theorem rough_affine_comp_eval {R : Type*} [CommSemiring R]
    (P : R[X]) (a b z : ℕ) :
    (P.comp (C (a : R) + C (b : R) * X)).eval (z : R) = P.eval ((a + b * z : ℕ) : R) := by
  simp only [eval_comp, eval_add, eval_C, eval_mul, eval_X, Nat.cast_add, Nat.cast_mul]

end Hindman168
