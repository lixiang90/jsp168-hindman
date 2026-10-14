import Hindman168.UnitriangularLieGroup
import Hindman168.StrictMatrixSmoothProjection
import Hindman168.UnitriangularAnalyticExponential

/-! The actual nilpotent matrix exponential and its constructed logarithm
are global smooth inverses for the native matrix Lie-group structure.
The logarithm is the retained finite residual-correction algorithm, not a
supplied smooth inverse. Comparison with arbitrary Lie-group exponentials
and their native tangent Lie brackets is a separate remaining task. -/

namespace Hindman168
open Matrix Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

local instance strictMatrixModelTopology (n : ℕ) :
    TopologicalSpace (StrictUpperTriangular n ℝ) :=
  (inferInstance : NormedAddCommGroup (StrictUpperTriangular n ℝ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

 theorem strictMatrixModelTopology_eq_original (n : ℕ) :
    strictMatrixModelTopology n = TopologicalSpace.induced
      (fun X : StrictUpperTriangular n ℝ => X.val)
      (inferInstance : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ)) := rfl

local instance strictMatrixSelfChart (n : ℕ) :
    ChartedSpace (StrictUpperTriangular n ℝ) (StrictUpperTriangular n ℝ) :=
  chartedSpaceSelf (StrictUpperTriangular n ℝ)

variable {n : ℕ} {r : ℕ∞ω}

 theorem matrixFiniteExp_contDiff :
    ContDiff ℝ r (matrixFiniteExp : Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) := by
  unfold matrixFiniteExp
  exact ContDiff.sum fun k _ =>
    (contDiff_matrix_pow (contDiff_id :
      ContDiff ℝ r (id : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)) k).const_smul ((k.factorial : ℚ)⁻¹)

 theorem unitriangularLogIteration_coordinates_contDiff (k : ℕ) :
    ContDiff ℝ r (fun t : UnitriangularIndex n → ℝ =>
      unitriangularLogIteration (unitriangularCoordinatesEquiv.symm t) k) := by
  induction k with
  | zero => exact contDiff_const
  | succ k ih =>
    change ContDiff ℝ r (fun t : UnitriangularIndex n → ℝ =>
      unitriangularLogIteration (unitriangularCoordinatesEquiv.symm t) k +
        (unitriangularCoordinateMatrix t -
          matrixFiniteExp (unitriangularLogIteration (unitriangularCoordinatesEquiv.symm t) k)))
    exact ih.add (unitriangularCoordinateMatrix_contDiff.sub (matrixFiniteExp_contDiff.comp ih))

 theorem unitriangularLogarithm_coordinates_contDiff :
    ContDiff ℝ r (fun t : UnitriangularIndex n → ℝ =>
      unitriangularLogarithm (unitriangularCoordinatesEquiv.symm t)) := by
  have h := (strictUpperTriangularProjection_contDiff (n := n) (r := r)).comp
    (unitriangularLogIteration_coordinates_contDiff (n := n) (r := r) n)
  have heq : (fun t : UnitriangularIndex n → ℝ =>
      strictUpperTriangularProjection n
        (unitriangularLogIteration (unitriangularCoordinatesEquiv.symm t) n)) =
      fun t => unitriangularLogarithm (unitriangularCoordinatesEquiv.symm t) := by
    funext t
    exact strictUpperTriangularProjection_coe (unitriangularLogarithm _)
  simpa only [Function.comp_def, heq] using h

 theorem unitriangularExponential_contMDiff :
    ContMDiff 𝓘(ℝ, StrictUpperTriangular n ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (unitriangularExponential : StrictUpperTriangular n ℝ → Unitriangular n ℝ) := by
  apply ContMDiff.of_comp_isOpenEmbedding (unitriangularCoordinatesHomeomorph :
    Unitriangular n ℝ ≃ₜ (UnitriangularIndex n → ℝ)).isOpenEmbedding
  have hE : ContDiff ℝ r (fun A : StrictUpperTriangular n ℝ => matrixFiniteExp A.val) :=
    matrixFiniteExp_contDiff.comp (StrictUpperTriangular n ℝ).subtypeL.contDiff
  apply ContDiff.contMDiff
  apply contDiff_pi.mpr
  intro p
  exact (contDiff_apply_apply ℝ ℝ (unitriangularRow p) (unitriangularColumn p)).comp hE

 theorem unitriangularLogarithm_contMDiff :
    ContMDiff 𝓘(ℝ, UnitriangularIndex n → ℝ) 𝓘(ℝ, StrictUpperTriangular n ℝ) r
      (unitriangularLogarithm : Unitriangular n ℝ → StrictUpperTriangular n ℝ) := by
  have h := unitriangularLogarithm_coordinates_contDiff.contMDiff.comp
    (unitriangularCoordinates_contMDiff (n := n) (r := r))
  have hleft (g : Unitriangular n ℝ) :
      unitriangularCoordinatesEquiv.symm (unitriangularCoordinates g) = g :=
    unitriangularCoordinatesEquiv.symm_apply_apply g
  simpa only [Function.comp_def, hleft] using h

 noncomputable def unitriangularExponentialDiffeomorph :
    Diffeomorph 𝓘(ℝ, StrictUpperTriangular n ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ)
      (StrictUpperTriangular n ℝ) (Unitriangular n ℝ) r where
  toEquiv := unitriangularExponentialEquiv
  contMDiff_toFun := unitriangularExponential_contMDiff
  contMDiff_invFun := unitriangularLogarithm_contMDiff

 theorem unitriangularOneParameter_contMDiff (X : StrictUpperTriangular n ℝ) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, UnitriangularIndex n → ℝ) r
      (fun t : ℝ => unitriangularExponential (t • X)) :=
  unitriangularExponential_contMDiff.comp
    ((contDiff_id.smul contDiff_const : ContDiff ℝ r (fun t : ℝ => t • X)).contMDiff)

end Hindman168
