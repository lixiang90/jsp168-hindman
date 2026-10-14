import Mathlib.LinearAlgebra.Matrix.Nondegenerate

namespace Matrix

theorem mulVec_injective_of_det_ne_zero {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [NoZeroDivisors R] {A : Matrix ι ι R} (hA : A.det ≠ 0) :
    Function.Injective A.mulVec := by
  intro x y hxy
  have hz : A.mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA hz)

end Matrix
