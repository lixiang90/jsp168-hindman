import Hindman168.UnitriangularTangentCoordinates
import Hindman168.UnitriangularTangentMatrices

/-! The actual native left-invariant field is calculated by differentiating
left multiplication in the original global chart. Its affine derivative
then computes the native Lie bracket, with the associative commutator sign. -/

namespace Hindman168
open Matrix
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable {n : ℕ}

 theorem unitriangular_left_multiply_coordinate_hasFDerivAt
    (g : Unitriangular n ℝ) (t : UnitriangularIndex n → ℝ) :
    HasFDerivAt (fun t : UnitriangularIndex n → ℝ =>
      unitriangularCoordinates (g * unitriangularCoordinatesEquiv.symm t))
      (unitriangularLeftTangentMap g) t := by
  have heq := funext (unitriangular_left_multiply_coordinate_affine g)
  rw [heq]
  exact (unitriangularLeftTangentMap g).hasFDerivAt.const_add (unitriangularCoordinates g)

 theorem unitriangular_mfderiv_mul_left (g h : Unitriangular n ℝ) :
    mfderiv 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (fun x : Unitriangular n ℝ => g * x) h = unitriangularLeftTangentMap g := by
  have hf : MDifferentiableAt 𝓘(ℝ, UnitriangularIndex n → ℝ)
      𝓘(ℝ, UnitriangularIndex n → ℝ) (fun x : Unitriangular n ℝ => g * x) h :=
    (contMDiff_mul_left (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (n := 1)).contMDiffAt.mdifferentiableAt
      (by simp)
  rw [unitriangular_mfderiv_eq_chart_fderiv _ _ hf]
  exact (unitriangular_left_multiply_coordinate_hasFDerivAt g (unitriangularCoordinates h)).fderiv

 theorem unitriangular_mulInvariantVectorField
    (v : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ))
    (g : Unitriangular n ℝ) :
    mulInvariantVectorField v g = unitriangularLeftTangentMap g v := by
  unfold mulInvariantVectorField
  erw [unitriangular_mfderiv_mul_left]
  rfl

 theorem unitriangular_invariant_field_coordinates
    (v : UnitriangularIndex n → ℝ)
    (t : UnitriangularIndex n → ℝ) :
    mulInvariantVectorField (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (G := Unitriangular n ℝ) v (unitriangularCoordinatesEquiv.symm t) =
      v + unitriangularFieldDerivative v t := by
  rw [unitriangular_mulInvariantVectorField, unitriangularLeftTangentMap_apply]
  exact unitriangular_coordinate_field_affine v t

 theorem unitriangular_invariant_field_coordinates_hasFDerivAt
    (v : UnitriangularIndex n → ℝ)
    (t : UnitriangularIndex n → ℝ) :
    HasFDerivAt (fun t : UnitriangularIndex n → ℝ =>
      (mulInvariantVectorField (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (G := Unitriangular n ℝ) v (unitriangularCoordinatesEquiv.symm t) : UnitriangularIndex n → ℝ))
      (unitriangularFieldDerivative v) t := by
  have heq := funext (unitriangular_invariant_field_coordinates v)
  rw [heq]
  exact (unitriangularFieldDerivative v).hasFDerivAt.const_add (v : UnitriangularIndex n → ℝ)

 theorem unitriangular_native_bracket_coordinates
    (v w : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    (⁅v, w⁆ : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) =
      matrixOffDiagonalCoordinates n
        (unitriangularTangentMatrix n v * unitriangularTangentMatrix n w -
          unitriangularTangentMatrix n w * unitriangularTangentMatrix n v) := by
  rw [GroupLieAlgebra.bracket_def, unitriangular_mlieBracket_coordinates,
    unitriangularCoordinates_one]
  change fderiv ℝ (fun t : UnitriangularIndex n → ℝ =>
      (mulInvariantVectorField w (unitriangularCoordinatesEquiv.symm t) : UnitriangularIndex n → ℝ)) 0
      (mulInvariantVectorField v (unitriangularCoordinatesEquiv.symm 0)) -
    fderiv ℝ (fun t : UnitriangularIndex n → ℝ =>
      (mulInvariantVectorField v (unitriangularCoordinatesEquiv.symm t) : UnitriangularIndex n → ℝ)) 0
      (mulInvariantVectorField w (unitriangularCoordinatesEquiv.symm 0)) = _
  rw [(unitriangular_invariant_field_coordinates_hasFDerivAt w 0).fderiv,
    (unitriangular_invariant_field_coordinates_hasFDerivAt v 0).fderiv]
  erw [unitriangular_invariant_field_coordinates v 0,
    unitriangular_invariant_field_coordinates w 0]
  simp only [map_zero, add_zero, unitriangularFieldDerivative_apply, map_sub]

end Hindman168
