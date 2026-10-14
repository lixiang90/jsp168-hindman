import Hindman168.LieOneParameterVelocity
import Hindman168.UnitriangularNativeLieAlgebra
import Hindman168.UnitriangularExponentialSmooth
import Hindman168.UnitriangularOneParameterLattice
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Identification of the actual finite matrix exponential with the general
native Lie-group exponential constructed from invariant integral curves.
The finite polynomial has its proved zero-time derivative; the original
one-parameter group law and general uniqueness then give the comparison.
No exponential comparison or global differential equation is assumed. -/

namespace Hindman168
open Matrix Function Set Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable {n : ℕ}

 theorem matrixFiniteExp_smul_hasDerivAt_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => matrixFiniteExp (t • A)) A 0 := by
  have ht (r : ℕ) : HasDerivAt
      (fun t : ℝ => ((r + 2).factorial : ℚ)⁻¹ • (t • A) ^ (r + 2)) 0 0 := by
    have h := ((hasDerivAt_pow (r + 2) (0 : ℝ)).smul_const (A ^ (r + 2))).const_smul
      (((r + 2).factorial : ℚ)⁻¹)
    convert! h using 1 <;> simp [smul_pow, show r + 2 - 1 = r + 1 by omega]
    funext t
    rfl
  have hs : HasDerivAt
      (fun t : ℝ => ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • (t • A) ^ (r + 2)) 0 0 := by
    convert! HasDerivAt.fun_sum (u := Finset.range n) (fun r _ => ht r) using 1
    simp only [Finset.sum_const_zero]
  have hl : HasDerivAt (fun t : ℝ => t • A) A 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const A using 1
    simp only [one_smul]
  have heq : (fun t : ℝ => matrixFiniteExp (t • A)) =
      fun t => 1 + t • A + ∑ r ∈ Finset.range n, ((r + 2).factorial : ℚ)⁻¹ • (t • A) ^ (r + 2) :=
    funext fun t => matrixFiniteExp_expansion (t • A)
  rw [heq]
  convert! (hl.const_add (1 : Matrix (Fin n) (Fin n) ℝ)).add hs using 1
  simp only [add_zero]

 theorem unitriangularExponential_zero :
    unitriangularExponential (0 : StrictUpperTriangular n ℝ) = 1 := by
  apply unitriangular_val_injective
  exact matrixFiniteExp_zero

 theorem unitriangularOneParameter_coordinates_hasDerivAt_zero (X : StrictUpperTriangular n ℝ) :
    HasDerivAt (fun t : ℝ => unitriangularCoordinates (unitriangularExponential (t • X)))
      (matrixOffDiagonalCoordinates n X.val) 0 := by
  change HasDerivAt (fun t : ℝ => matrixOffDiagonalCoordinates n
    (matrixFiniteExp (t • X.val))) (matrixOffDiagonalCoordinates n X.val) 0
  exact (matrixOffDiagonalCoordinates n).hasFDerivAt.comp_hasDerivAt 0
    (matrixFiniteExp_smul_hasDerivAt_zero X.val)

 theorem unitriangularOneParameter_hasMFDerivAt_zero (X : StrictUpperTriangular n ℝ) :
    HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (fun t : ℝ => unitriangularExponential (t • X)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (matrixOffDiagonalCoordinates n X.val)) := by
  have hi : HasMFDerivAt 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ)
      0 (ContinuousLinearMap.id ℝ (UnitriangularIndex n → ℝ)) := by
    have hd : MDifferentiableAt 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
        (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ) 0 :=
      (unitriangularCoordinates_inverse_contMDiff (r := 1)).contMDiffAt.mdifferentiableAt (by simp)
    exact hd.hasMFDerivAt.congr_mfderiv (unitriangularCoordinates_inverse_mfderiv 0)
  have hzero : unitriangularCoordinates (unitriangularExponential ((0 : ℝ) • X)) = 0 := by
    rw [zero_smul, unitriangularExponential_zero, unitriangularCoordinates_one]
  have hi' : HasMFDerivAt 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (unitriangularCoordinatesEquiv.symm : (UnitriangularIndex n → ℝ) → Unitriangular n ℝ)
      (unitriangularCoordinates (unitriangularExponential ((0 : ℝ) • X)))
      (ContinuousLinearMap.id ℝ (UnitriangularIndex n → ℝ)) := by
    convert hi using 1
  have hc := (unitriangularOneParameter_coordinates_hasDerivAt_zero X).hasFDerivAt.hasMFDerivAt
  have h := hi'.comp 0 hc
  have heq : unitriangularCoordinatesEquiv.symm ∘
      (fun t : ℝ => unitriangularCoordinates (unitriangularExponential (t • X))) =
      (fun t : ℝ => unitriangularExponential (t • X)) :=
    funext fun t => unitriangularCoordinatesEquiv.symm_apply_apply (unitriangularExponential (t • X))
  rw [heq] at h
  exact h.congr_mfderiv (ContinuousLinearMap.id_comp _)

 theorem unitriangular_native_oneParameter_curve_eq (X : StrictUpperTriangular n ℝ) :
    (fun t : ℝ => unitriangularExponential (t • X)) =
      lieOneParameterCurve (I := 𝓘(ℝ, UnitriangularIndex n → ℝ))
        (G := Unitriangular n ℝ) (matrixOffDiagonalCoordinates n X.val) := by
  apply lie_oneParameter_eq_curve_from_zero
  · rw [zero_smul, unitriangularExponential_zero]
  · exact unitriangularExponential_smul_add X
  · exact unitriangularOneParameter_hasMFDerivAt_zero X

 theorem unitriangular_nativeExponential_eq
    (v : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    nativeLieExponential (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (G := Unitriangular n ℝ) v = unitriangularExponential (unitriangularNativeLieEquiv n v) := by
  have h := congrFun (unitriangular_native_oneParameter_curve_eq
    (unitriangularNativeLieEquiv n v)) 1
  rw [unitriangularNativeLieEquiv_value, matrixOffDiagonalCoordinates_tangentMatrix] at h
  simpa only [nativeLieExponential, one_smul] using h.symm

 theorem unitriangular_nativeExponential_inverse_eq (X : UnitriangularLieAlgebra n ℝ) :
    nativeLieExponential (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (G := Unitriangular n ℝ)
      ((unitriangularNativeLieEquiv n).symm X) = unitriangularExponential X := by
  rw [unitriangular_nativeExponential_eq, LieEquiv.apply_symm_apply]

 theorem unitriangular_nativeExponential_analytic_value
    (v : GroupLieAlgebra 𝓘(ℝ, UnitriangularIndex n → ℝ) (Unitriangular n ℝ)) :
    ((nativeLieExponential (I := 𝓘(ℝ, UnitriangularIndex n → ℝ)) (G := Unitriangular n ℝ) v).val : Matrix (Fin n) (Fin n) ℝ) =
      NormedSpace.exp (unitriangularTangentMatrix n v) := by
  rw [unitriangular_nativeExponential_eq, unitriangularExponential_analytic_value,
    unitriangularNativeLieEquiv_value]

end Hindman168
