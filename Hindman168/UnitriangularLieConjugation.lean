import Hindman168.UnitriangularLieAlgebra
import Mathlib.Algebra.Ring.Action.ConjAct

/-! Actual unitriangular matrix conjugation is a linear Lie equivalence of
strict matrices and preserves every support layer. Multiplication is actual
matrix multiplication and the map is constructed, not supplied. -/

namespace Hindman168
open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]
local instance conjugationMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) := LieRing.ofAssociativeRing

 def unitriangularConjugationRingHom (g : Unitriangular n R) :
    Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) R :=
  MulSemiringAction.toRingHom (ConjAct (Matrix (Fin n) (Fin n) R)ˣ)
    (Matrix (Fin n) (Fin n) R) (ConjAct.toConjAct g.val)

 theorem unitriangularConjugationRingHom_apply (g : Unitriangular n R) (A : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom g A =
      (g.val : Matrix (Fin n) (Fin n) R) * A * (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) := rfl

 theorem MatrixDepth.unitriangular_conjugate {k : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : MatrixDepth k A) (g : Unitriangular n R) :
    MatrixDepth k (unitriangularConjugationRingHom g A) := by
  have hu : MatrixDepth 0 (g.val : Matrix (Fin n) (Fin n) R) := unitriangular_matrixDepth_zero g
  have hv : MatrixDepth 0 (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) :=
    unitriangular_matrixDepth_zero (g⁻¹)
  rw [unitriangularConjugationRingHom_apply]
  simpa only [Nat.zero_add, Nat.add_zero] using (hu.mul hA).mul hv

 def unitriangularConjugationLieHom (g : Unitriangular n R) :
    UnitriangularLieAlgebra n R →ₗ⁅R⁆ UnitriangularLieAlgebra n R where
  toFun A := ⟨unitriangularConjugationRingHom g A.val, A.property.unitriangular_conjugate g⟩
  map_add' A B := Subtype.ext (map_add (unitriangularConjugationRingHom g) A.val B.val)
  map_smul' c A := by
    apply Subtype.ext
    change (g.val : Matrix (Fin n) (Fin n) R) * (c • A.val) * (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) =
      c • ((g.val : Matrix (Fin n) (Fin n) R) * A.val * (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R))
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  map_lie' {A B} := by
    apply Subtype.ext
    change unitriangularConjugationRingHom g (A.val * B.val - B.val * A.val) =
      unitriangularConjugationRingHom g A.val * unitriangularConjugationRingHom g B.val -
        unitriangularConjugationRingHom g B.val * unitriangularConjugationRingHom g A.val
    rw [map_sub, map_mul, map_mul]

 theorem unitriangularConjugation_inverse (g : Unitriangular n R) (A : UnitriangularLieAlgebra n R) :
    unitriangularConjugationLieHom g⁻¹ (unitriangularConjugationLieHom g A) = A := by
  apply Subtype.ext
  change (ConjAct.toConjAct g.val)⁻¹ • (ConjAct.toConjAct g.val • A.val) = A.val
  exact inv_smul_smul _ _

 theorem unitriangularConjugation_depth_iff (g : Unitriangular n R)
    (A : UnitriangularLieAlgebra n R) (k : ℕ) :
    MatrixDepth k (unitriangularConjugationLieHom g A).val ↔ MatrixDepth k A.val := by
  constructor
  · intro h
    have hi := h.unitriangular_conjugate g⁻¹
    have he := congrArg (fun B : UnitriangularLieAlgebra n R => B.val)
      (unitriangularConjugation_inverse g A)
    exact he ▸ hi
  · intro h
    exact h.unitriangular_conjugate g

 def unitriangularConjugationLieEquiv (g : Unitriangular n R) :
    UnitriangularLieAlgebra n R ≃ₗ⁅R⁆ UnitriangularLieAlgebra n R where
  toFun := unitriangularConjugationLieHom g
  invFun := unitriangularConjugationLieHom g⁻¹
  left_inv := unitriangularConjugation_inverse g
  right_inv A := by simpa only [inv_inv] using unitriangularConjugation_inverse g⁻¹ A
  map_add' := (unitriangularConjugationLieHom g).map_add
  map_smul' := (unitriangularConjugationLieHom g).map_smul
  map_lie' {A B} := (unitriangularConjugationLieHom g).map_lie A B

end Hindman168
