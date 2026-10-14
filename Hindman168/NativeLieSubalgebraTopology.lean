import Hindman168.NativeLieSubalgebraSubgroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The actual original exponential restricted to an original native
Lie subalgebra is a homeomorphism onto its genuine original subgroup,
with the natural subtype topology. True finite-dimensional closure and
convexity give closed, contractible and simply connected subgroups. No
specified-lattice cocompactness follows from these topological facts alone. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraExponentialHomeomorph
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    nativeLieSubalgebraModel (E := E) S ≃ₜ nativeLieSubalgebraSubgroup (E := E) S where
  toFun v := ⟨nativeLieExponential (I := I) (G := G) v.val, ⟨v.val, v.property, rfl⟩⟩
  invFun g := ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val,
    (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff S g.val).mp g.property⟩
  left_inv v := Subtype.ext (nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.val)
  right_inv g := Subtype.ext (nativeLieExponential_globalLogarithm (I := I) (G := G) g.val)
  continuous_toFun :=
    ((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _

 theorem nativeLieSubalgebraSubgroup_closed
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    IsClosed (nativeLieSubalgebraSubgroup (E := E) S : Set G) := by
  have he : (nativeLieSubalgebraSubgroup (E := E) S : Set G) =
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ⁻¹'
        (nativeLieSubalgebraModel S : Set E) :=
    Set.ext (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff S)
  rw [he]
  exact (nativeLieSubalgebraModel_closed S).preimage
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous

 theorem nativeLieSubalgebraSubgroup_contractible
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    ContractibleSpace (nativeLieSubalgebraSubgroup (E := E) S) := by
  let V : Submodule ℝ E := nativeLieSubalgebraModel S
  letI : ContractibleSpace V := V.convex.contractibleSpace ⟨0, V.zero_mem⟩
  exact (nativeLieSubalgebraExponentialHomeomorph S).symm.contractibleSpace

 theorem nativeLieSubalgebraSubgroup_simplyConnected
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    SimplyConnectedSpace (nativeLieSubalgebraSubgroup (E := E) S) := by
  letI := nativeLieSubalgebraSubgroup_contractible S
  infer_instance

 theorem nativeLieSubalgebraSubgroup_connected
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    ConnectedSpace (nativeLieSubalgebraSubgroup (E := E) S) := by
  letI := nativeLieSubalgebraSubgroup_contractible S
  infer_instance

end Hindman168
