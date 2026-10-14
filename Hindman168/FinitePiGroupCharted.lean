import Hindman168.HomeomorphSingletonDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace Hindman168
open scoped Manifold ContDiff

variable {ι : Type*} [Fintype ι] {E F H G : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners ℝ (F i) (H i)}
  [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] [∀ i, Group (G i)]
  (e : ∀ i, Diffeomorph 𝓘(ℝ, E i) (I i) (E i) (G i) ∞)

noncomputable def finitePiGroupHomeomorph : (∀ i, E i) ≃ₜ (∀ i, G i) :=
  Homeomorph.piCongrRight (fun i => (e i).toHomeomorph)

@[reducible]
noncomputable def finitePiGroupChartedSpace : ChartedSpace (∀ i, E i) (∀ i, G i) :=
  homeomorphSingletonChart (finitePiGroupHomeomorph e)

theorem finitePiGroup_isManifold :
    letI := finitePiGroupChartedSpace e
    IsManifold 𝓘(ℝ, ∀ i, E i) ∞ (∀ i, G i) :=
  homeomorphSingletonChart_isManifold (finitePiGroupHomeomorph e)

noncomputable def finitePiGroupDiffeomorph :
    letI := finitePiGroupChartedSpace e
    Diffeomorph 𝓘(ℝ, ∀ i, E i) 𝓘(ℝ, ∀ i, E i) (∀ i, E i) (∀ i, G i) ∞ :=
  homeomorphSingletonDiffeomorph (finitePiGroupHomeomorph e)

theorem finitePiGroup_coordinate_contMDiff (i : ι) :
    letI := finitePiGroupChartedSpace e
    ContMDiff 𝓘(ℝ, ∀ i, E i) (I i) ∞ (fun g : ∀ i, G i => g i) := by
  letI := finitePiGroupChartedSpace e
  have hp : ContDiff ℝ ∞ (fun x : ∀ i, E i => x i) := contDiff_pi.mp contDiff_id i
  have h := (e i).contMDiff_toFun.comp (hp.contMDiff.comp (finitePiGroupDiffeomorph e).contMDiff_invFun)
  exact h.congr (fun g => ((e i).apply_symm_apply (g i)).symm)

theorem finitePiGroup_contMDiff_from_normed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ∀ i, G i) (hf : ∀ i, ContMDiff 𝓘(ℝ, V) (I i) ∞ (fun x => f x i)) :
    letI := finitePiGroupChartedSpace e
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ∀ i, E i) ∞ f := by
  letI := finitePiGroupChartedSpace e
  have hc : ContDiff ℝ ∞ (fun x i => (e i).symm (f x i)) :=
    contDiff_pi.mpr (fun i => ((e i).contMDiff_invFun.comp (hf i)).contDiff)
  have h := (finitePiGroupDiffeomorph e).contMDiff_toFun.comp hc.contMDiff
  exact h.congr (fun x => funext (fun i => ((e i).apply_symm_apply (f x i)).symm))

theorem finitePiGroup_map_contMDiff (f : ∀ i, G i → G i)
    (hf : ∀ i, ContMDiff (I i) (I i) ∞ (f i)) :
    letI := finitePiGroupChartedSpace e
    ContMDiff 𝓘(ℝ, ∀ i, E i) 𝓘(ℝ, ∀ i, E i) ∞ (fun (g : ∀ i, G i) i => f i (g i)) := by
  letI := finitePiGroupChartedSpace e
  let d := finitePiGroupDiffeomorph e
  have h : ContMDiff 𝓘(ℝ, ∀ i, E i) 𝓘(ℝ, ∀ i, E i) ∞ (fun x i => f i (d x i)) := by
    apply finitePiGroup_contMDiff_from_normed e
    intro i
    have hp : ContDiff ℝ ∞ (fun x : ∀ i, E i => x i) := contDiff_pi.mp contDiff_id i
    exact (hf i).comp ((e i).contMDiff_toFun.comp hp.contMDiff)
  exact (h.comp d.contMDiff_invFun).congr (fun g => by
    change (fun i => f i (g i)) = (fun i => f i (d (d.symm g) i))
    rw [d.apply_symm_apply])

end Hindman168
