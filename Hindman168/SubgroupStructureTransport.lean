import Hindman168.NativeNilmanifoldData

/-! Actual subgroup chart/Lie structures transport along a PROVED
literal subgroup equality while retaining original topology and operations. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {G : Type*} [Group G] [TopologicalSpace G]

@[reducible]
noncomputable def subgroupChartedSpaceOfEq {H : Type*} [TopologicalSpace H]
    (N M : Subgroup G) (h : N=M) (c : ChartedSpace H N) : ChartedSpace H M := by
  cases h
  exact c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

theorem subgroup_lieGroup_of_eq (N M : Subgroup G) (h : N=M) (c : ChartedSpace H N) :
    letI := c
    letI := subgroupChartedSpaceOfEq N M h c
    LieGroup I ∞ N → LieGroup I ∞ M := by
  cases h
  intro hN
  exact hN

theorem subgroup_boundaryless_of_eq (N M : Subgroup G) (h : N=M) (c : ChartedSpace H N) :
    letI := c
    letI := subgroupChartedSpaceOfEq N M h c
    BoundarylessManifold I N → BoundarylessManifold I M := by
  cases h
  intro hN
  exact hN

end Hindman168
