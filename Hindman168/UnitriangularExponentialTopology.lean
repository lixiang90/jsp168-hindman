import Hindman168.UnitriangularExponentialInverse
import Hindman168.UnitriangularCoordinates

/-! The genuine nilpotent matrix exponential is a global homeomorphism.
Both directions are finite polynomial expressions in actual matrix entries;
no norm, abstract logarithm or assumed exponential bijection is used. -/

namespace Hindman168
open Matrix Topology

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
  [TopologicalSpace R] [IsTopologicalRing R] [ContinuousConstSMul ℚ R]

 theorem matrixFiniteExp_continuous :
    Continuous (matrixFiniteExp : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R) := by
  unfold matrixFiniteExp
  apply continuous_finsetSum
  intro r _
  exact (show Continuous (fun A : Matrix (Fin n) (Fin n) R => A ^ r) from
    (continuous_id : Continuous (id : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)).pow r).const_smul ((r.factorial : ℚ)⁻¹)

 theorem unitriangularLogIteration_continuous (r : ℕ) :
    Continuous (fun g : Unitriangular n R => unitriangularLogIteration g r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    have hval : Continuous (fun g : Unitriangular n R =>
        (g.val : Matrix (Fin n) (Fin n) R)) :=
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).comp continuous_subtype_val
    exact ih.add (hval.sub (matrixFiniteExp_continuous.comp ih))

 theorem unitriangularExponential_continuous :
    Continuous (unitriangularExponential : StrictUpperTriangular n R → Unitriangular n R) := by
  have hE : Continuous (fun A : StrictUpperTriangular n R => matrixFiniteExp A.val) :=
    matrixFiniteExp_continuous.comp continuous_subtype_val
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact hE
  · have heq : (fun A : StrictUpperTriangular n R =>
        (↑(unitriangularExponential A).val⁻¹ : Matrix (Fin n) (Fin n) R)) =
        fun A => (matrixFiniteExp A.val).adjugate := by
      funext A
      exact unitriangular_inverse_adjugate _
    change Continuous (fun A : StrictUpperTriangular n R =>
      (↑(unitriangularExponential A).val⁻¹ : Matrix (Fin n) (Fin n) R))
    rw [heq]
    exact hE.matrix_adjugate

 theorem unitriangularLogarithm_continuous :
    Continuous (unitriangularLogarithm : Unitriangular n R → StrictUpperTriangular n R) := by
  exact (unitriangularLogIteration_continuous n).subtype_mk _

 noncomputable def unitriangularExponentialHomeomorph :
    StrictUpperTriangular n R ≃ₜ Unitriangular n R where
  toEquiv := unitriangularExponentialEquiv
  continuous_toFun := unitriangularExponential_continuous
  continuous_invFun := unitriangularLogarithm_continuous

end Hindman168
