import Hindman168.DiscreteCosetGlobalCharts

namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup J ∞ G] [IsTopologicalGroup G]
  (e : Diffeomorph 𝓘(ℝ, E) J E G ∞) (Γ : Subgroup G) [DiscreteTopology Γ]

theorem discreteCosetGlobal_isManifold :
    letI := discreteCosetGlobalChartedSpace e Γ
    IsManifold 𝓘(ℝ, E) ∞ (G ⧸ Γ) := by
  letI := discreteCosetGlobalChartedSpace e Γ
  apply isManifold_of_contDiffOn 𝓘(ℝ, E) ∞ (G ⧸ Γ)
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ x hx
  have hx' : discreteCosetModelProjection e Γ x ∈ (discreteCosetModelChart e Γ b).source := by
    have hh := hx.1.2
    change (discreteCosetModelChart e Γ a).symm x ∈ (discreteCosetModelChart e Γ b).source at hh
    rwa [discreteCosetModelChart_symm] at hh
  change ContDiffWithinAt ℝ ∞
    (fun y => discreteCosetModelChart e Γ b ((discreteCosetModelChart e Γ a).symm y)) _ x
  rw [discreteCosetModelChart_symm]
  exact (discreteCosetModelChart_lift_contDiffAt e Γ b x hx').contDiffWithinAt

end Hindman168
