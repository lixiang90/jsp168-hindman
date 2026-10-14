import Hindman168.UnitriangularLieGroup
import Hindman168.StrictMatrixSmoothProjection
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! Actual linear tangent-to-matrix coordinates, and the affine coordinate
formulas for left multiplication and invariant fields. All matrix products
are the original associative products. -/

namespace Hindman168
open Matrix
open scoped Manifold ContDiff Matrix.Norms.Elementwise

 noncomputable def unitriangularTangentMatrixLinear (n : ℕ) :
    (UnitriangularIndex n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun v i j := if h : i < j then v ⟨toLex (OrderDual.toDual i, j), h⟩ else 0
  map_add' v w := by
    ext i j
    by_cases h : i < j <;> simp [h]
  map_smul' c v := by
    ext i j
    by_cases h : i < j <;> simp [h]

 noncomputable def unitriangularTangentMatrix (n : ℕ) :
    (UnitriangularIndex n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap (unitriangularTangentMatrixLinear n)

 noncomputable def matrixOffDiagonalCoordinatesLinear (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (UnitriangularIndex n → ℝ) where
  toFun A p := A (unitriangularRow p) (unitriangularColumn p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 noncomputable def matrixOffDiagonalCoordinates (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (UnitriangularIndex n → ℝ) :=
  LinearMap.toContinuousLinearMap (matrixOffDiagonalCoordinatesLinear n)

variable {n : ℕ}

 theorem unitriangularTangentMatrix_strict (v : UnitriangularIndex n → ℝ) :
    MatrixDepth 1 (unitriangularTangentMatrix n v) := by
  intro i j h
  have hij : ¬ i < j := by
    intro hij
    have := Fin.lt_def.mp hij
    omega
  change (if h : i < j then v ⟨toLex (OrderDual.toDual i, j), h⟩ else 0) = 0
  simp only [dif_neg hij]

 theorem matrixOffDiagonalCoordinates_tangentMatrix (v : UnitriangularIndex n → ℝ) :
    matrixOffDiagonalCoordinates n (unitriangularTangentMatrix n v) = v := by
  funext p
  change (if h : unitriangularRow p < unitriangularColumn p then
      v ⟨toLex (OrderDual.toDual (unitriangularRow p), unitriangularColumn p), h⟩ else 0) = v p
  rw [dif_pos p.property]
  rfl

 theorem unitriangularTangentMatrix_offDiagonal {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : MatrixDepth 1 A) :
    unitriangularTangentMatrix n (matrixOffDiagonalCoordinates n A) = A := by
  ext i j
  change (if h : i < j then A i j else 0) = A i j
  by_cases hij : i < j
  · simp only [dif_pos hij]
  · have hz := hA i j (by
      have := Fin.le_iff_val_le_val.mp (le_of_not_gt hij)
      omega)
    simp only [dif_neg hij, hz]

 theorem unitriangularCoordinateMatrix_eq_one_add (v : UnitriangularIndex n → ℝ) :
    unitriangularCoordinateMatrix v = 1 + unitriangularTangentMatrix n v := by
  ext i j
  by_cases hij : i < j
  · have hne : i ≠ j := ne_of_lt hij
    simp [unitriangularCoordinateMatrix, unitriangularTangentMatrix,
      unitriangularTangentMatrixLinear, hij, hne]
  · simp [unitriangularCoordinateMatrix, unitriangularTangentMatrix,
      unitriangularTangentMatrixLinear, hij, Matrix.one_apply]

 theorem matrixOffDiagonalCoordinates_one :
    matrixOffDiagonalCoordinates n (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  funext p
  change (1 : Matrix (Fin n) (Fin n) ℝ) (unitriangularRow p) (unitriangularColumn p) = 0
  simp [ne_of_lt p.property]

 theorem unitriangularCoordinates_eq_offDiagonal (g : Unitriangular n ℝ) :
    unitriangularCoordinates g = matrixOffDiagonalCoordinates n
      (g.val : Matrix (Fin n) (Fin n) ℝ) := rfl

 theorem unitriangularCoordinates_one :
    unitriangularCoordinates (1 : Unitriangular n ℝ) = 0 :=
  matrixOffDiagonalCoordinates_one

 theorem unitriangularCoordinateMatrix_zero :
    unitriangularCoordinateMatrix (0 : UnitriangularIndex n → ℝ) = 1 := by
  rw [unitriangularCoordinateMatrix_eq_one_add, map_zero, add_zero]

 noncomputable def unitriangularLeftTangentMap (g : Unitriangular n ℝ) :
    (UnitriangularIndex n → ℝ) →L[ℝ] (UnitriangularIndex n → ℝ) :=
  (matrixOffDiagonalCoordinates n).comp
    ((LinearMap.toContinuousLinearMap
      (mulLeftLinearMap (Fin n) ℝ (g.val : Matrix (Fin n) (Fin n) ℝ))).comp
        (unitriangularTangentMatrix n))

 theorem unitriangularLeftTangentMap_apply (g : Unitriangular n ℝ) (v : UnitriangularIndex n → ℝ) :
    unitriangularLeftTangentMap g v = matrixOffDiagonalCoordinates n
      ((g.val : Matrix (Fin n) (Fin n) ℝ) * unitriangularTangentMatrix n v) := rfl

 noncomputable def unitriangularFieldDerivative (v : UnitriangularIndex n → ℝ) :
    (UnitriangularIndex n → ℝ) →L[ℝ] (UnitriangularIndex n → ℝ) :=
  (matrixOffDiagonalCoordinates n).comp
    ((LinearMap.toContinuousLinearMap
      (mulRightLinearMap (Fin n) ℝ (unitriangularTangentMatrix n v))).comp
        (unitriangularTangentMatrix n))

 theorem unitriangularFieldDerivative_apply (v w : UnitriangularIndex n → ℝ) :
    unitriangularFieldDerivative v w = matrixOffDiagonalCoordinates n
      (unitriangularTangentMatrix n w * unitriangularTangentMatrix n v) := rfl

 theorem unitriangular_left_multiply_coordinate_affine
    (g : Unitriangular n ℝ) (t : UnitriangularIndex n → ℝ) :
    unitriangularCoordinates (g * unitriangularCoordinatesEquiv.symm t) =
      unitriangularCoordinates g + unitriangularLeftTangentMap g t := by
  change matrixOffDiagonalCoordinates n
    ((g.val : Matrix (Fin n) (Fin n) ℝ) * unitriangularCoordinateMatrix t) = _
  rw [unitriangularCoordinateMatrix_eq_one_add, Matrix.mul_add, Matrix.mul_one, map_add]
  rfl

 theorem unitriangular_coordinate_field_affine (v t : UnitriangularIndex n → ℝ) :
    matrixOffDiagonalCoordinates n (unitriangularCoordinateMatrix t * unitriangularTangentMatrix n v) =
      v + unitriangularFieldDerivative v t := by
  rw [unitriangularCoordinateMatrix_eq_one_add, Matrix.add_mul, Matrix.one_mul, map_add,
    matrixOffDiagonalCoordinates_tangentMatrix]
  rfl

end Hindman168
