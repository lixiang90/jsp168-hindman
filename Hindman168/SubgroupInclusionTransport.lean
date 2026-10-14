import Hindman168.SubgroupStructureTransport
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! Original subgroup inclusion smoothness and identity derivative are
preserved along PROVED literal subgroup/chart equality. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G]

theorem subgroup_inclusion_contMDiff_of_eq (N M : Subgroup G) (h : N=M)
    (c : ChartedSpace H N) :
    letI := c
    letI := subgroupChartedSpaceOfEq N M h c
    ContMDiff I J ∞ ((↑) : N → G) → ContMDiff I J ∞ ((↑) : M → G) := by
  cases h
  intro hN
  exact hN

theorem subgroup_inclusion_mfderiv_of_eq (N M : Subgroup G) (h : N=M)
    (c : ChartedSpace H N) (L : E →L[ℝ] F) :
    letI := c
    letI := subgroupChartedSpaceOfEq N M h c
    mfderiv I J ((↑) : N → G) 1 = L → mfderiv I J ((↑) : M → G) 1 = L := by
  cases h
  intro hN
  exact hN

end Hindman168
