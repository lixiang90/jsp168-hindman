import Hindman168.NativeCenterQuotientRelation
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Algebra.Module.Basic

/-! The genuine original exponential diffeomorphism descends to an actual
homeomorphism from the original real center-model quotient to the
original group center quotient. This uses proved equivalence of the
actual relations, not a supplied quotient inverse or Lie structure. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterQuotientExponentialHomeomorph :
    (E ⧸ nativeLieCenterModel (I := I) (G := G)) ≃ₜ (G ⧸ Subgroup.center G) :=
  Homeomorph.Quotient.congr
    (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)).toHomeomorph (by
      intro v w
      exact (Submodule.quotientRel_def (nativeLieCenterModel (I := I) (G := G))).trans
        ((nativeLieCenter_coset_relation (I := I) (G := G) v w).trans
          QuotientGroup.leftRel_apply.symm))

theorem nativeCenterQuotientExponentialHomeomorph_mk (v : E) :
    nativeCenterQuotientExponentialHomeomorph (I := I) (G := G) (Submodule.Quotient.mk v) =
      QuotientGroup.mk (nativeLieExponential (I := I) (G := G) v) := rfl

theorem nativeCenterQuotientExponentialHomeomorph_symm_mk (g : G) :
    (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)).symm (QuotientGroup.mk g) =
      Submodule.Quotient.mk (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := rfl

theorem nativeCenterQuotientExponentialHomeomorph_zero :
    nativeCenterQuotientExponentialHomeomorph (I := I) (G := G) 0 = 1 := by
  change (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) (0 : E)) :
    G ⧸ Subgroup.center G) = 1
  exact congrArg (QuotientGroup.mk : G → G ⧸ Subgroup.center G)
    (nativeLieExponential_zero (I := I) (G := G))

include I in
theorem nativeCenterQuotient_contractible : ContractibleSpace (G ⧸ Subgroup.center G) :=
  (nativeCenterQuotientExponentialHomeomorph (E := E) (I := I) (G := G)).symm.contractibleSpace

include I in
theorem nativeCenterQuotient_simplyConnected : SimplyConnectedSpace (G ⧸ Subgroup.center G) := by
  letI : ContractibleSpace (G ⧸ Subgroup.center G) := nativeCenterQuotient_contractible (I := I)
  infer_instance

end Hindman168
