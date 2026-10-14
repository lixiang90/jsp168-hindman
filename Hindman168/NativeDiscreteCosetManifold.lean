import Hindman168.DiscreteCosetGlobalSmooth
import Hindman168.NativeLieExponentialDiffeomorph

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

@[reducible]
noncomputable def nativeDiscreteCosetChartedSpace (Γ : Subgroup G) [DiscreteTopology Γ] :
    ChartedSpace E (G ⧸ Γ) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact discreteCosetGlobalChartedSpace (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)) Γ

theorem nativeDiscreteCoset_isManifold (Γ : Subgroup G) [DiscreteTopology Γ] :
    letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
    IsManifold 𝓘(ℝ, E) ∞ (G ⧸ Γ) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact discreteCosetGlobal_isManifold (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)) Γ

theorem nativeDiscreteCoset_projection_contMDiff (Γ : Subgroup G) [DiscreteTopology Γ] :
    letI := nativeDiscreteCosetChartedSpace (E := E) (I := I) Γ
    ContMDiff I 𝓘(ℝ, E) ∞ (QuotientGroup.mk (s := Γ)) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact discreteCosetProjection_contMDiff (nativeLieExponentialDiffeomorph (E := E) (I := I) (G := G)) Γ

end Hindman168
