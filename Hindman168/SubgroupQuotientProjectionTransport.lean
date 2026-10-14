import Hindman168.SubgroupQuotientStructureTransport
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! Smoothness and the actual model differential of the ORIGINAL quotient
projection are preserved along a PROVED equality of actual subgroups/charts. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]

theorem subgroup_quotient_projection_contMDiff_of_eq (N M : Subgroup G) (h : N=M)
    (c : ChartedSpace H' (G ⧸ N)) :
    letI := c
    letI := subgroupQuotientChartedSpaceOfEq N M h c
    ContMDiff I J ∞ ((↑) : G → G ⧸ N) → ContMDiff I J ∞ ((↑) : G → G ⧸ M) := by
  cases h
  intro hN
  exact hN

theorem subgroup_quotient_projection_mfderiv_of_eq (N M : Subgroup G) (h : N=M)
    (c : ChartedSpace H' (G ⧸ N)) (x : G) (L : E →L[ℝ] F) :
    letI := c
    letI := subgroupQuotientChartedSpaceOfEq N M h c
    mfderiv I J ((↑) : G → G ⧸ N) x = L → mfderiv I J ((↑) : G → G ⧸ M) x = L := by
  cases h
  intro hN
  exact hN

end Hindman168
