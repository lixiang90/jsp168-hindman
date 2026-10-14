import Hindman168.DiscreteCosetGlobalManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup J ∞ G] [IsTopologicalGroup G]
  (e : Diffeomorph 𝓘(ℝ, E) J E G ∞) (Γ : Subgroup G) [DiscreteTopology Γ]

theorem discreteCosetModelProjection_contMDiff :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (discreteCosetModelProjection e Γ) := by
  letI := discreteCosetGlobalChartedSpace e Γ
  letI := discreteCosetGlobal_isManifold e Γ
  intro x
  have ha : discreteCosetModelChart e Γ x ∈ atlas E (G ⧸ Γ) := ⟨x, rfl⟩
  have hx : x ∈ (discreteCosetModelChart e Γ x).target :=
    (discreteCosetModelProjection_localHomeomorph e Γ).self_mem_localInverseAt_target
  have h := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (IsManifold.subset_maximalAtlas ha) hx
  rwa [discreteCosetModelChart_symm] at h

theorem discreteCosetProjection_contMDiff :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiff J 𝓘(ℝ, E) ∞ (QuotientGroup.mk (s := Γ)) := by
  letI := discreteCosetGlobalChartedSpace e Γ
  have h := (discreteCosetModelProjection_contMDiff e Γ).comp e.contMDiff_invFun
  exact h.congr (fun g => by
    change QuotientGroup.mk g = QuotientGroup.mk (e (e.symm g))
    rw [e.apply_symm_apply])

theorem discreteCosetModelChart_contMDiffAt (a : E) {y : G ⧸ Γ}
    (hy : y ∈ (discreteCosetModelChart e Γ a).source) :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (discreteCosetModelChart e Γ a) y := by
  letI := discreteCosetGlobalChartedSpace e Γ
  letI := discreteCosetGlobal_isManifold e Γ
  exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨a, rfl⟩) hy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners ℝ V H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem discreteCoset_contMDiff_of_modelProjection (f : G ⧸ Γ → N)
    (hf : ContMDiff 𝓘(ℝ, E) K ∞ (f ∘ discreteCosetModelProjection e Γ)) :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiff 𝓘(ℝ, E) K ∞ f := by
  letI := discreteCosetGlobalChartedSpace e Γ
  intro y
  let a := e.symm y.out
  let c := discreteCosetModelChart e Γ a
  have hy : y ∈ c.source := ChartedSpace.mem_chart_source y
  have hc := discreteCosetModelChart_contMDiffAt e Γ a hy
  have h := hf.contMDiffAt.comp y hc
  apply h.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hy] with z hz
  change f z = f (discreteCosetModelProjection e Γ (c z))
  rw [discreteCosetModelChart_right e Γ a hz]

theorem discreteCoset_contMDiff_of_projection (f : G ⧸ Γ → N)
    (hf : ContMDiff J K ∞ (f ∘ QuotientGroup.mk (s := Γ))) :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiff 𝓘(ℝ, E) K ∞ f := by
  apply discreteCoset_contMDiff_of_modelProjection e Γ f
  exact hf.comp e.contMDiff_toFun

end Hindman168
