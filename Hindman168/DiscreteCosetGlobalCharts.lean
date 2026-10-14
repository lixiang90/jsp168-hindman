import Hindman168.DiscreteCosetSmoothLifts
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsTopologicalGroup G]
  (e : Diffeomorph 𝓘(ℝ, E) J E G ∞) (Γ : Subgroup G) [DiscreteTopology Γ]

noncomputable def discreteCosetModelProjection (x : E) : G ⧸ Γ := QuotientGroup.mk (e x)

theorem discreteCosetModelProjection_localHomeomorph :
    IsLocalHomeomorph (discreteCosetModelProjection e Γ) :=
  (Γ.isQuotientCoveringMap (isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap.isLocalHomeomorph.comp
    e.toHomeomorph.isLocalHomeomorph

noncomputable def discreteCosetModelChart (x : E) : OpenPartialHomeomorph (G ⧸ Γ) E :=
  (discreteCosetModelProjection_localHomeomorph e Γ).localInverseAt x

theorem discreteCosetModelChart_symm (x : E) :
    (discreteCosetModelChart e Γ x).symm = discreteCosetModelProjection e Γ :=
  (discreteCosetModelProjection_localHomeomorph e Γ).localInverseAt_symm x

theorem discreteCosetModelChart_right (x : E) {y : G ⧸ Γ}
    (hy : y ∈ (discreteCosetModelChart e Γ x).source) :
    discreteCosetModelProjection e Γ (discreteCosetModelChart e Γ x y) = y :=
  (discreteCosetModelProjection_localHomeomorph e Γ).apply_localInverseAt_of_mem hy

@[reducible]
noncomputable def discreteCosetGlobalChartedSpace : ChartedSpace E (G ⧸ Γ) where
  atlas := Set.range (discreteCosetModelChart e Γ)
  chartAt y := discreteCosetModelChart e Γ (e.symm y.out)
  mem_chart_source y := by
    have h := (discreteCosetModelProjection_localHomeomorph e Γ).apply_self_mem_localInverseAt_source
      (x := e.symm y.out)
    have he : discreteCosetModelProjection e Γ (e.symm y.out) = y := by
      change QuotientGroup.mk (e (e.symm y.out)) = y
      rw [e.apply_symm_apply]
      exact Quotient.out_eq y
    rw [he] at h
    exact h
  chart_mem_atlas y := ⟨e.symm y.out, rfl⟩

theorem discreteCosetModelChart_lift_contDiffAt [LieGroup J ∞ G] (a x : E)
    (hx : discreteCosetModelProjection e Γ x ∈ (discreteCosetModelChart e Γ a).source) :
    ContDiffAt ℝ ∞ (fun y => discreteCosetModelChart e Γ a (discreteCosetModelProjection e Γ y)) x := by
  let p := discreteCosetModelProjection e Γ
  let c := discreteCosetModelChart e Γ a
  have hp : Continuous p := (discreteCosetModelProjection_localHomeomorph e Γ).continuous
  have hc : ContinuousAt (fun y => c (p y)) x := (c.continuousAt hx).comp hp.continuousAt
  have hmem : ∀ᶠ y in 𝓝 x, p y ∈ c.source := hp.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds hx)
  have hl : ContMDiffAt 𝓘(ℝ, E) J ∞ (fun y => e (c (p y))) x := by
    apply discreteCoset_contMDiffAt_lift Γ e.contMDiff_toFun.contMDiffAt
      (e.continuous.continuousAt.comp hc)
    exact hmem.mono (fun y hy => (discreteCosetModelChart_right e Γ a hy).symm)
  have hs := e.contMDiff_invFun.contMDiffAt.comp x hl
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun y => e.symm (e (c (p y)))) x at hs
  have he : (fun y => e.symm (e (c (p y)))) = (fun y => c (p y)) :=
    funext (fun _ => e.symm_apply_apply _)
  rw [he] at hs
  exact hs.contDiffAt

end Hindman168
