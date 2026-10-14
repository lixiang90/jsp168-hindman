import Hindman168.NativeCenterQuotientNormedModel
import Hindman168.HomeomorphSingletonDiffeomorph

/-! The actual center quotient keeps its original quotient topology and
receives the constructed single global chart coming from its true
exponential homeomorphism. This yields a genuine smooth coordinate
identification, without yet assuming quotient operations are smooth. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeCenterQuotientChartedSpace :
    ChartedSpace (E ⧸ nativeLieCenterModel (I := I) (G := G)) (G ⧸ Subgroup.center G) :=
  homeomorphSingletonChart (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G))

theorem nativeCenterQuotient_isManifold :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    IsManifold 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)) ∞ (G ⧸ Subgroup.center G) :=
  homeomorphSingletonChart_isManifold (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G))

noncomputable def nativeCenterQuotientExponentialDiffeomorph :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    Diffeomorph 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
      𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
      (E ⧸ nativeLieCenterModel (I := I) (G := G)) (G ⧸ Subgroup.center G) ∞ :=
  homeomorphSingletonDiffeomorph (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G))

end Hindman168
