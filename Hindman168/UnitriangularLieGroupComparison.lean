import Hindman168.UnitriangularLieLowerCentral
import Hindman168.UnitriangularLowerCentralExact
import Hindman168.UnitriangularExponentialDepth
import Hindman168.UnitriangularExponentialContractible
import Hindman168.UnitriangularAnalyticExponential

/-! The actual matrix exponential identifies Lie and group lower central
layers exactly. This follows from two independently computed series, not
from an assumed Lie-group correspondence. The natural restricted maps are
homeomorphisms; arbitrary original nilpotent Lie groups remain outside this
concrete comparison. -/

namespace Hindman168
open Matrix Set Topology

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
local instance comparisonMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) := LieRing.ofAssociativeRing

 theorem unitriangularLie_exponential_lowerCentral_iff (A : UnitriangularLieAlgebra n R) (k : ℕ) :
    A ∈ LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k ↔
      unitriangularExponential A ∈ (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k := by
  rw [unitriangularLie_lowerCentral_eq_depth, unitriangular_lowerCentral_eq_depth]
  change MatrixDepth (k + 1) A.val ↔ UnitriangularDepth (k + 1) (unitriangularExponential A)
  exact (unitriangularExponential_depth_iff A (k + 1)).symm

 theorem unitriangularLie_logarithm_lowerCentral_iff (g : Unitriangular n R) (k : ℕ) :
    unitriangularLogarithm g ∈
      LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k ↔
      g ∈ (⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k := by
  have h := unitriangularLie_exponential_lowerCentral_iff (unitriangularLogarithm g) k
  rw [unitriangularExponential_logarithm] at h
  exact h

 theorem unitriangularLie_exponential_lowerCentral_image (k : ℕ) :
    (unitriangularExponential : UnitriangularLieAlgebra n R → Unitriangular n R) ''
      (LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k :
        Set (UnitriangularLieAlgebra n R)) =
      ((⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k : Set (Unitriangular n R)) := by
  ext g
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (unitriangularLie_exponential_lowerCentral_iff A k).mp hA
  · intro hg
    exact ⟨unitriangularLogarithm g, (unitriangularLie_logarithm_lowerCentral_iff g k).mpr hg,
      unitriangularExponential_logarithm g⟩

 noncomputable def unitriangularLowerCentralExponentialEquiv (k : ℕ) :
    (LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k) ≃
      ((⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k) where
  toFun A := ⟨unitriangularExponential A.val,
    (unitriangularLie_exponential_lowerCentral_iff A.val k).mp A.property⟩
  invFun g := ⟨unitriangularLogarithm g.val,
    (unitriangularLie_logarithm_lowerCentral_iff g.val k).mpr g.property⟩
  left_inv A := Subtype.ext (unitriangularLogarithm_exponential A.val)
  right_inv g := Subtype.ext (unitriangularExponential_logarithm g.val)

variable [TopologicalSpace R] [IsTopologicalRing R] [ContinuousConstSMul ℚ R]

 theorem unitriangularLowerCentralExponential_continuous (k : ℕ) :
    Continuous (unitriangularLowerCentralExponentialEquiv (n := n) (R := R) k) := by
  have hE : Continuous (unitriangularExponential : UnitriangularLieAlgebra n R → Unitriangular n R) :=
    unitriangularExponential_continuous
  exact (hE.comp continuous_subtype_val).subtype_mk _

 theorem unitriangularLowerCentralLogarithm_continuous (k : ℕ) :
    Continuous (unitriangularLowerCentralExponentialEquiv (n := n) (R := R) k).symm := by
  have hL : Continuous (unitriangularLogarithm : Unitriangular n R → UnitriangularLieAlgebra n R) :=
    unitriangularLogarithm_continuous
  exact (hL.comp continuous_subtype_val).subtype_mk _

 noncomputable def unitriangularLowerCentralExponentialHomeomorph (k : ℕ) :
    (LieModule.lowerCentralSeries R (UnitriangularLieAlgebra n R) (UnitriangularLieAlgebra n R) k) ≃ₜ
      ((⊤ : Subgroup (Unitriangular n R)).lowerCentralSeries k) where
  toEquiv := unitriangularLowerCentralExponentialEquiv k
  continuous_toFun := unitriangularLowerCentralExponential_continuous k
  continuous_invFun := unitriangularLowerCentralLogarithm_continuous k

 theorem unitriangular_real_lowerCentral_contractible (k : ℕ) :
    ContractibleSpace ((⊤ : Subgroup (Unitriangular n ℝ)).lowerCentralSeries k) := by
  letI : ContinuousAdd (UnitriangularLieAlgebra n ℝ) :=
    inferInstanceAs (ContinuousAdd (StrictUpperTriangular n ℝ))
  letI : ContinuousSMul ℝ (UnitriangularLieAlgebra n ℝ) :=
    inferInstanceAs (ContinuousSMul ℝ (StrictUpperTriangular n ℝ))
  let L := LieModule.lowerCentralSeries ℝ (UnitriangularLieAlgebra n ℝ) (UnitriangularLieAlgebra n ℝ) k
  have hc : Convex ℝ (L : Set (UnitriangularLieAlgebra n ℝ)) :=
    (L : Submodule ℝ (UnitriangularLieAlgebra n ℝ)).convex
  letI : ContractibleSpace L := hc.contractibleSpace ⟨0, L.zero_mem⟩
  exact (unitriangularLowerCentralExponentialHomeomorph (n := n) (R := ℝ) k).symm.contractibleSpace

 theorem unitriangular_real_lowerCentral_simplyConnected (k : ℕ) :
    SimplyConnectedSpace ((⊤ : Subgroup (Unitriangular n ℝ)).lowerCentralSeries k) := by
  letI := unitriangular_real_lowerCentral_contractible (n := n) k
  infer_instance

 theorem unitriangular_real_lowerCentral_connected (k : ℕ) :
    ConnectedSpace ((⊤ : Subgroup (Unitriangular n ℝ)).lowerCentralSeries k) := by
  letI := unitriangular_real_lowerCentral_contractible (n := n) k
  infer_instance

end Hindman168
