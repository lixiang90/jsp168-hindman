import Hindman168.NativeCentralSubspaceCosetRelation
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceQuotientExponentialHomeomorph (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    (E ⧸ V) ≃ₜ (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) :=
  Homeomorph.Quotient.congr
    (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)).toHomeomorph (by
      intro v w
      exact (Submodule.quotientRel_def V).trans
        ((nativeCentralSubspace_coset_relation V hV v w).trans QuotientGroup.leftRel_apply.symm))

theorem nativeCentralSubspaceQuotientExponentialHomeomorph_mk (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (v : E) :
    nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV (Submodule.Quotient.mk v) =
      QuotientGroup.mk (nativeLieExponential (I := I) (G := G) v) := rfl

theorem nativeCentralSubspaceQuotientExponentialHomeomorph_symm_mk (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (g : G) :
    (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV).symm (QuotientGroup.mk g) =
      Submodule.Quotient.mk (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := rfl

theorem nativeCentralSubspaceQuotient_contractible (V : Submodule ℝ E)
    [IsClosed (V : Set E)] (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    ContractibleSpace (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) :=
  (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV).symm.contractibleSpace

theorem nativeCentralSubspaceQuotient_simplyConnected (V : Submodule ℝ E)
    [IsClosed (V : Set E)] (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    SimplyConnectedSpace (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) := by
  letI := nativeCentralSubspaceQuotient_contractible (I := I) V hV
  infer_instance

end Hindman168
