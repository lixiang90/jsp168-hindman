import Hindman168.NativeLieSubalgebraTopology
import Hindman168.HomeomorphSingletonDiffeomorph

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeLieSubalgebraChartedSpace
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    ChartedSpace (nativeLieSubalgebraModel (E := E) S) (nativeLieSubalgebraSubgroup (E := E) S) :=
  homeomorphSingletonChart (nativeLieSubalgebraExponentialHomeomorph (E := E) S)

theorem nativeLieSubalgebra_isManifold (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    IsManifold 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) ∞ (nativeLieSubalgebraSubgroup (E := E) S) :=
  homeomorphSingletonChart_isManifold (nativeLieSubalgebraExponentialHomeomorph (E := E) S)

noncomputable def nativeLieSubalgebraExponentialDiffeomorph
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    Diffeomorph 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
      𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)
      (nativeLieSubalgebraModel (E := E) S) (nativeLieSubalgebraSubgroup (E := E) S) ∞ :=
  homeomorphSingletonDiffeomorph (nativeLieSubalgebraExponentialHomeomorph (E := E) S)

end Hindman168

