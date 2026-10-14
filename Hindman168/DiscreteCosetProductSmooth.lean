import Hindman168.DiscreteCosetGlobalSmooth

/-! Smooth descent with an additional parameter. The quotient need not be
by a normal subgroup. Both variables vary simultaneously. -/
namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E F V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup J ∞ G] [IsTopologicalGroup G]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ V HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ W HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

theorem discreteCoset_product_contMDiff_of_projection
    (e : Diffeomorph 𝓘(ℝ, E) J E G ∞) (Γ : Subgroup G) [DiscreteTopology Γ]
    (f : P × (G ⧸ Γ) → N)
    (hf : ContMDiff (IP.prod J) IN ∞
      (fun p : P × G => f (p.1, QuotientGroup.mk p.2))) :
    letI := discreteCosetGlobalChartedSpace e Γ
    ContMDiff (IP.prod 𝓘(ℝ, E)) IN ∞ f := by
  letI := discreteCosetGlobalChartedSpace e Γ
  have hm : ContMDiff (IP.prod 𝓘(ℝ, E)) IN ∞
      (fun p : P × E => f (p.1, discreteCosetModelProjection e Γ p.2)) :=
    hf.comp (contMDiff_fst.prodMk (e.contMDiff_toFun.comp contMDiff_snd))
  intro y
  let a := e.symm y.2.out
  let c := discreteCosetModelChart e Γ a
  have hy : y.2 ∈ c.source := ChartedSpace.mem_chart_source y.2
  have hs : ContMDiffAt (IP.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : P × (G ⧸ Γ) => p.2) y := contMDiffAt_snd
  have hc := (discreteCosetModelChart_contMDiffAt e Γ a hy).comp y hs
  have h := hm.contMDiffAt.comp y (contMDiffAt_fst.prodMk hc)
  apply h.congr_of_eventuallyEq
  have hn : ∀ᶠ p : P × (G ⧸ Γ) in 𝓝 y, p.2 ∈ c.source :=
    hs.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hy)
  filter_upwards [hn] with p hp
  change f p = f (p.1, discreteCosetModelProjection e Γ (c p.2))
  rw [discreteCosetModelChart_right e Γ a hp]

end Hindman168
