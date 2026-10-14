import Hindman168.FinitePiGroupCharted
import Mathlib.Geometry.Manifold.Algebra.LieGroup

namespace Hindman168
open scoped Manifold ContDiff

variable {ι : Type*} [Fintype ι] {E F H G : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners ℝ (F i) (H i)}
  [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] [∀ i, Group (G i)]
  (e : ∀ i, Diffeomorph 𝓘(ℝ, E i) (I i) (E i) (G i) ∞)

variable [∀ i, LieGroup (I i) ∞ (G i)]

theorem finitePiGroup_mul_contMDiff :
    letI := finitePiGroupChartedSpace e
    let J := 𝓘(ℝ, ∀ i, E i)
    ContMDiff (J.prod J) J ∞ (fun p : (∀ i, G i) × (∀ i, G i) => p.1 * p.2) := by
  letI := finitePiGroupChartedSpace e
  let d := finitePiGroupDiffeomorph e
  let V := ∀ i, E i
  have h : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ, V) ∞
      (fun p : V × V => d p.1 * d p.2) := by
    apply finitePiGroup_contMDiff_from_normed e
    intro i
    have hp : ContDiff ℝ ∞ (fun x : V => x i) := contDiff_pi.mp contDiff_id i
    exact ((e i).contMDiff_toFun.comp (hp.contMDiff.comp contDiff_fst.contMDiff)).mul
      ((e i).contMDiff_toFun.comp (hp.contMDiff.comp contDiff_snd.contMDiff))
  have hh := h.comp ((d.contMDiff_invFun.comp contMDiff_fst).prodMk_space
    (d.contMDiff_invFun.comp contMDiff_snd))
  exact hh.congr (fun p => by
    change p.1 * p.2 = d (d.symm p.1) * d (d.symm p.2)
    rw [d.apply_symm_apply, d.apply_symm_apply])

theorem finitePiGroup_inv_contMDiff :
    letI := finitePiGroupChartedSpace e
    let J := 𝓘(ℝ, ∀ i, E i)
    ContMDiff J J ∞ (fun g : ∀ i, G i => g⁻¹) := by
  letI := finitePiGroupChartedSpace e
  let d := finitePiGroupDiffeomorph e
  have h : ContMDiff 𝓘(ℝ, ∀ i, E i) 𝓘(ℝ, ∀ i, E i) ∞
      (fun x => (d x)⁻¹) := by
    apply finitePiGroup_contMDiff_from_normed e
    intro i
    have hp : ContDiff ℝ ∞ (fun x : ∀ i, E i => x i) := contDiff_pi.mp contDiff_id i
    exact ((e i).contMDiff_toFun.comp hp.contMDiff).inv
  exact (h.comp d.contMDiff_invFun).congr (fun g => by
    change g⁻¹ = (d (d.symm g))⁻¹
    rw [d.apply_symm_apply])

theorem finitePiGroup_lieGroup :
    letI := finitePiGroupChartedSpace e
    LieGroup 𝓘(ℝ, ∀ i, E i) ∞ (∀ i, G i) := by
  letI := finitePiGroupChartedSpace e
  letI := finitePiGroup_isManifold e
  exact { contMDiff_mul := finitePiGroup_mul_contMDiff e
          contMDiff_inv := finitePiGroup_inv_contMDiff e }

end Hindman168
