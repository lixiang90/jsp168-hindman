import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-! The actual unit upper-triangular subgroup of the general linear group.
All multiplication and inversion are those of matrix units. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

 def IsUnitriangular (A : Matrix (Fin n) (Fin n) R) : Prop :=
  A.BlockTriangular id ∧ ∀ i, A i i = 1

 theorem upperTriangular_mul_diagonal {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA hk, zero_mul]
    · rw [hB hk, mul_zero]
  · simp

 theorem isUnitriangular_one : IsUnitriangular (1 : Matrix (Fin n) (Fin n) R) := by
  exact ⟨Matrix.blockTriangular_one, by intro i; simp⟩

 theorem IsUnitriangular.mul {A B : Matrix (Fin n) (Fin n) R}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) : IsUnitriangular (A * B) := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  intro i
  rw [upperTriangular_mul_diagonal hA.1 hB.1, hA.2, hB.2, one_mul]

 theorem IsUnitriangular.inv (u : Matrix.GeneralLinearGroup (Fin n) R)
    (hu : IsUnitriangular (u : Matrix (Fin n) (Fin n) R)) :
    IsUnitriangular (↑u⁻¹ : Matrix (Fin n) (Fin n) R) := by
  letI : Invertible (u : Matrix (Fin n) (Fin n) R) := u.invertible
  have hb : (↑u⁻¹ : Matrix (Fin n) (Fin n) R).BlockTriangular id := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hu.1
  refine ⟨hb, ?_⟩
  intro i
  have hm : (u : Matrix (Fin n) (Fin n) R) * (↑u⁻¹ : Matrix (Fin n) (Fin n) R) = 1 :=
    u.val_inv
  have hd := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i i) hm
  rw [upperTriangular_mul_diagonal hu.1 hb, hu.2, one_mul] at hd
  simpa using hd

 def unitriangularSubgroup (n : ℕ) (R : Type*) [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) R) where
  carrier := {u | IsUnitriangular (u : Matrix (Fin n) (Fin n) R)}
  one_mem' := isUnitriangular_one
  mul_mem' hA hB := hA.mul hB
  inv_mem' hu := hu.inv _

 abbrev Unitriangular (n : ℕ) (R : Type*) [CommRing R] := unitriangularSubgroup n R

 theorem IsUnitriangular.det_eq_one {A : Matrix (Fin n) (Fin n) R}
    (hA : IsUnitriangular A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular hA.1]
  simp only [hA.2, Finset.prod_const_one]

 noncomputable def unitriangularOfMatrix (A : Matrix (Fin n) (Fin n) R)
    (hA : IsUnitriangular A) : Unitriangular n R :=
  ⟨Matrix.GeneralLinearGroup.mk'' A (hA.det_eq_one ▸ isUnit_one), hA⟩

 @[simp] theorem unitriangularOfMatrix_val (A : Matrix (Fin n) (Fin n) R)
    (hA : IsUnitriangular A) :
    ((unitriangularOfMatrix A hA).val : Matrix (Fin n) (Fin n) R) = A := rfl

 theorem unitriangular_val_injective : Function.Injective
    (fun u : Unitriangular n R => (u.val : Matrix (Fin n) (Fin n) R)) := by
  intro u v h
  exact Subtype.ext (Units.ext h)

 theorem unitriangular_inverse_adjugate (u : Unitriangular n R) :
    (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) =
      (u.val : Matrix (Fin n) (Fin n) R).adjugate := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, u.property.det_eq_one]
  simp

 noncomputable def unitriangularTransvection (i j : Fin n) (hij : i < j) (c : R) :
    Unitriangular n R :=
  unitriangularOfMatrix (Matrix.transvection i j c) ⟨
    Matrix.blockTriangular_transvection hij.le c, by
      intro k
      simp [Matrix.transvection, Matrix.single]
      intro hik hjk
      exact False.elim ((ne_of_lt hij) (hik.trans hjk.symm))⟩

 @[simp] theorem unitriangularTransvection_val (i j : Fin n) (hij : i < j) (c : R) :
    ((unitriangularTransvection i j hij c).val : Matrix (Fin n) (Fin n) R) =
      Matrix.transvection i j c := rfl

end Hindman168
