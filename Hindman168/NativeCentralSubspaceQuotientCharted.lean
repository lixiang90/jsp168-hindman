import Hindman168.NativeCentralSubspaceQuotientHomeomorph
import Hindman168.HomeomorphSingletonDiffeomorph
import Hindman168.ClosedFiniteRealQuotientSection

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
  (V : Submodule ℝ E) [IsClosed (V : Set E)]
  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

@[reducible]
noncomputable def nativeCentralSubspaceQuotientChartedSpace :
    ChartedSpace (E ⧸ V) (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) :=
  homeomorphSingletonChart (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV)

theorem nativeCentralSubspaceQuotient_isManifold :
    letI := nativeCentralSubspaceQuotientChartedSpace V hV
    IsManifold 𝓘(ℝ, E ⧸ V) ∞ (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) :=
  homeomorphSingletonChart_isManifold (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV)

noncomputable def nativeCentralSubspaceQuotientExponentialDiffeomorph :
    letI := nativeCentralSubspaceQuotientChartedSpace V hV
    Diffeomorph 𝓘(ℝ, E ⧸ V) 𝓘(ℝ, E ⧸ V) (E ⧸ V)
      (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) ∞ :=
  homeomorphSingletonDiffeomorph (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV)

theorem nativeCentralSubspaceQuotient_t2Space :
    T2Space (G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) :=
  (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV).t2Space

omit [IsClosed (V : Set E)] in
theorem nativeCentralSubspaceQuotientExponentialHomeomorph_zero :
    nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV 0 = 1 := by
  change (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) (0 : E)) :
    G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV) = 1
  exact congrArg (QuotientGroup.mk : G → G ⧸ nativeCentralSubspaceSubgroup (I := I) V hV)
    (nativeLieExponential_zero (I := I) (G := G))

end Hindman168
