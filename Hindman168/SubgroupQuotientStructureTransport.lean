import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Algebra.Group.Quotient
import Hindman168.NativeNilmanifoldData

/-! Exact structure transport along PROVED equality of actual subgroups.
It preserves the quotient topology and actual group operations, not merely
an unproved identification of two manifolds. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {G : Type*} [Group G] [TopologicalSpace G]

@[reducible]
noncomputable def subgroupQuotientChartedSpaceOfEq {H : Type*} [TopologicalSpace H]
    (N M : Subgroup G) (h : N=M) (c : ChartedSpace H (G ⧸ N)) : ChartedSpace H (G ⧸ M) := by
  cases h
  exact c

theorem subgroup_quotient_t2_of_eq (N M : Subgroup G) (h : N=M) (hN : T2Space (G ⧸ N)) :
    T2Space (G ⧸ M) := by
  cases h
  exact hN

theorem subgroup_quotient_simplyConnected_of_eq (N M : Subgroup G) (h : N=M)
    (hN : SimplyConnectedSpace (G ⧸ N)) : SimplyConnectedSpace (G ⧸ M) := by
  cases h
  exact hN

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

theorem subgroup_quotient_lieGroup_of_eq (N M : Subgroup G) [N.Normal] [M.Normal]
    (h : N=M) (c : ChartedSpace H (G ⧸ N)) :
    letI := c
    letI := subgroupQuotientChartedSpaceOfEq N M h c
    LieGroup I ∞ (G ⧸ N) → LieGroup I ∞ (G ⧸ M) := by
  cases h
  intro hN
  exact hN

theorem subgroup_quotient_boundaryless_of_eq (N M : Subgroup G) (h : N=M)
    (c : ChartedSpace H (G ⧸ N)) :
    letI := c
    letI := subgroupQuotientChartedSpaceOfEq N M h c
    BoundarylessManifold I (G ⧸ N) → BoundarylessManifold I (G ⧸ M) := by
  cases h
  intro hN
  exact hN

end Hindman168
