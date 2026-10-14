import Hindman168.UnitriangularDepthCommutator

/-! Exact elementary matrix commutators over arbitrary commutative rings. -/

namespace Hindman168
open Matrix
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

 theorem unitriangularTransvection_inv (i j : Fin n) (hij : i < j) (c : R) :
    (unitriangularTransvection i j hij c)⁻¹ = unitriangularTransvection i j hij (-c) := by
  apply inv_eq_of_mul_eq_one_right
  apply unitriangular_val_injective
  change Matrix.transvection i j c * Matrix.transvection i j (-c) = 1
  calc
    _ = Matrix.transvection i j (c + (-c)) :=
      Matrix.transvection_mul_transvection_same i j (ne_of_lt hij) c (-c)
    _ = 1 := by rw [add_neg_cancel, Matrix.transvection_zero]

 theorem unitriangularTransvection_commutator (i j l : Fin n)
    (hij : i < j) (hjl : j < l) (a b : R) :
    ⁅unitriangularTransvection i j hij a, unitriangularTransvection j l hjl b⁆ =
      unitriangularTransvection i l (hij.trans hjl) (a * b) := by
  rw [commutatorElement_def, unitriangularTransvection_inv, unitriangularTransvection_inv]
  apply unitriangular_val_injective
  change Matrix.transvection i j a * Matrix.transvection j l b *
    Matrix.transvection i j (-a) * Matrix.transvection j l (-b) = Matrix.transvection i l (a * b)
  simp only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ (ne_of_lt hij).symm,
    Matrix.single_mul_single_of_ne _ _ _ _ (ne_of_lt hjl).symm,
    Matrix.single_mul_single_of_ne _ _ _ _ (ne_of_lt (hij.trans hjl)).symm]
  simp only [mul_neg, neg_mul, zero_mul, add_zero, ← Matrix.single_neg]
  abel

end Hindman168
