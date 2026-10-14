import Hindman168.UnitriangularSubalgebraStabilizer
import Hindman168.UnitriangularExponentialContractible
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual exponential image of a real matrix Lie subalgebra has its
natural subtype topology. A constructed restricted exponential homeomorphism
proves closedness and contractibility. These facts alone do not make the
image a subgroup; arbitrary product closure remains a separate BCH task. -/

namespace Hindman168
open Matrix Set Topology

variable {n : ℕ}
local instance subalgebraTopologyMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 def unitriangularSubalgebraDomain
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) : Submodule ℝ (StrictUpperTriangular n ℝ) :=
  V.toSubmodule.comap (StrictUpperTriangular n ℝ).subtype

 noncomputable def unitriangularSubalgebraExponentialEquiv
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    unitriangularSubalgebraDomain V ≃ unitriangularSubalgebraExpImage V where
  toFun X := ⟨unitriangularExponential X.val, by
    change (unitriangularLogarithm (unitriangularExponential X.val)).val ∈ V
    rw [unitriangularLogarithm_exponential]
    exact X.property⟩
  invFun g := ⟨unitriangularLogarithm g.val, g.property⟩
  left_inv X := Subtype.ext (unitriangularLogarithm_exponential X.val)
  right_inv g := Subtype.ext (unitriangularExponential_logarithm g.val)

 noncomputable def unitriangularSubalgebraExponentialHomeomorph
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    unitriangularSubalgebraDomain V ≃ₜ unitriangularSubalgebraExpImage V where
  toEquiv := unitriangularSubalgebraExponentialEquiv V
  continuous_toFun := (unitriangularExponential_continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (unitriangularLogarithm_continuous.comp continuous_subtype_val).subtype_mk _

 theorem unitriangularSubalgebraDomain_isClosed
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    IsClosed (unitriangularSubalgebraDomain V : Set (StrictUpperTriangular n ℝ)) :=
  (V.toSubmodule.closed_of_finiteDimensional).preimage continuous_subtype_val

 theorem unitriangularSubalgebraExpImage_isClosed
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    IsClosed (unitriangularSubalgebraExpImage V) :=
  (unitriangularSubalgebraDomain_isClosed V).preimage unitriangularLogarithm_continuous

 theorem unitriangularSubalgebraExpImage_contractible
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ContractibleSpace (unitriangularSubalgebraExpImage V) := by
  have hc : Convex ℝ (unitriangularSubalgebraDomain V : Set (StrictUpperTriangular n ℝ)) :=
    (unitriangularSubalgebraDomain V).convex
  letI : ContractibleSpace (unitriangularSubalgebraDomain V) :=
    hc.contractibleSpace ⟨0, (unitriangularSubalgebraDomain V).zero_mem⟩
  exact (unitriangularSubalgebraExponentialHomeomorph V).symm.contractibleSpace

 theorem unitriangularSubalgebraExpImage_simplyConnected
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    SimplyConnectedSpace (unitriangularSubalgebraExpImage V) := by
  letI := unitriangularSubalgebraExpImage_contractible V
  infer_instance

 theorem unitriangularSubalgebraExpImage_pathConnected
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    PathConnectedSpace (unitriangularSubalgebraExpImage V) := by
  letI := unitriangularSubalgebraExpImage_contractible V
  infer_instance

 theorem unitriangularSubalgebraExpImage_connected
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ConnectedSpace (unitriangularSubalgebraExpImage V) := by
  letI := unitriangularSubalgebraExpImage_contractible V
  infer_instance

 theorem unitriangularConjugationRingHom_continuous_group (Y : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun g : Unitriangular n ℝ => unitriangularConjugationRingHom g Y) := by
  have hv : Continuous (fun g : Unitriangular n ℝ => (g.val : Matrix (Fin n) (Fin n) ℝ)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous (fun g : Unitriangular n ℝ =>
      (↑g.val⁻¹ : Matrix (Fin n) (Fin n) ℝ)) := hv.comp continuous_inv
  exact (hv.mul continuous_const).mul hi

 theorem unitriangularSubalgebraStabilizer_isClosed
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    IsClosed (unitriangularSubalgebraStabilizer V : Set (Unitriangular n ℝ)) := by
  have hc : IsClosed (V : Set (Matrix (Fin n) (Fin n) ℝ)) :=
    V.toSubmodule.closed_of_finiteDimensional
  have hm : IsClosed {g : Unitriangular n ℝ |
      ∀ Y ∈ V, unitriangularConjugationRingHom g Y ∈ V} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun Y => isClosed_iInter fun _ =>
      hc.preimage (unitriangularConjugationRingHom_continuous_group Y)
  have heq : (unitriangularSubalgebraStabilizer V : Set (Unitriangular n ℝ)) =
      {g | ∀ Y ∈ V, unitriangularConjugationRingHom g Y ∈ V} ∩
      {g | ∀ Y ∈ V, unitriangularConjugationRingHom g⁻¹ Y ∈ V} := by
    ext g
    constructor
    · intro hg
      exact ⟨fun Y hY => (hg Y).mpr hY,
        fun Y hY => ((unitriangularSubalgebraStabilizer V).inv_mem hg Y).mpr hY⟩
    · rintro ⟨h1, h2⟩ Y
      constructor
      · intro hY
        have hi := h2 _ hY
        rwa [unitriangularConjugationRingHom_inv_cancel] at hi
      · exact h1 Y
  rw [heq]
  exact hm.inter (hm.preimage continuous_inv)

end Hindman168
