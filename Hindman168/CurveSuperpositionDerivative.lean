import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Actual superposition on continuous curves. A locally defined field
is used pointwise whenever its composition is continuous. Strict
Fréchet differentiability at a constant curve follows from the actual
strict derivative of the field, uniformly in the compact time variable. -/

namespace Hindman168
open Set Metric Filter Asymptotics Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

 noncomputable def curveSuperposition (f : E → F) (α : C(K, E)) : C(K, F) := by
  classical
  exact if h : Continuous (fun t => f (α t)) then ⟨fun t => f (α t), h⟩ else 0

 omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
 theorem curveSuperposition_apply_of_continuous (f : E → F) (α : C(K, E))
    (h : Continuous (fun t => f (α t))) (t : K) :
    curveSuperposition f α t = f (α t) := by
  simp only [curveSuperposition, dif_pos h, ContinuousMap.coe_mk]

 omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
 theorem curveSuperposition_const (f : E → F) (x : E) :
    curveSuperposition f (ContinuousMap.const K x) = ContinuousMap.const K (f x) := by
  ext t
  exact curveSuperposition_apply_of_continuous f _ (by simpa only [ContinuousMap.const_apply] using
    (continuous_const : Continuous (fun _ : K => f x))) t

 theorem curveSuperposition_hasStrictFDerivAt_const {f : E → F} {L : E →L[ℝ] F}
    {x : E} (hf : HasStrictFDerivAt f L x) :
    HasStrictFDerivAt (curveSuperposition (K := K) f) (ContinuousLinearMap.compLeftContinuous ℝ K L)
      (ContinuousMap.const K x) := by
  obtain ⟨C, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨d, hd, hds⟩ := Metric.mem_nhds_iff.mp hU
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  obtain ⟨W, hWo, hxW, hW⟩ := exists_nhds_square (hf.isLittleO.def hε)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds hxW)
  let δ := min d r
  have hδ : 0 < δ := lt_min hd hr
  have hmem (α : C(K, E)) (hα : α ∈ ball (ContinuousMap.const K x) δ) (t : K) :
      α t ∈ U ∧ α t ∈ W := by
    have ht : dist (α t) x < δ := by
      rw [mem_ball, dist_eq_norm] at hα
      rw [dist_eq_norm]
      exact lt_of_le_of_lt ((α - ContinuousMap.const K x).norm_coe_le_norm t) hα
    exact ⟨hds (lt_of_lt_of_le ht (min_le_left d r)),
      hrs (lt_of_lt_of_le ht (min_le_right d r))⟩
  filter_upwards [prod_mem_nhds
    (ball_mem_nhds (ContinuousMap.const K x) hδ)
    (ball_mem_nhds (ContinuousMap.const K x) hδ)] with p hp
  have hc₁ : Continuous (fun t => f (p.1 t)) := continuousOn_univ.mp
    (hLip.continuousOn.comp p.1.continuous.continuousOn
      (fun t _ => (hmem p.1 hp.1 t).1))
  have hc₂ : Continuous (fun t => f (p.2 t)) := continuousOn_univ.mp
    (hLip.continuousOn.comp p.2.continuous.continuousOn
      (fun t _ => (hmem p.2 hp.2 t).1))
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  change ‖curveSuperposition f p.1 t - curveSuperposition f p.2 t -
    L (p.1 t - p.2 t)‖ ≤ ε * ‖p.1 - p.2‖
  rw [curveSuperposition_apply_of_continuous f p.1 hc₁,
    curveSuperposition_apply_of_continuous f p.2 hc₂]
  have hb : ‖f (p.1 t) - f (p.2 t) - L (p.1 t - p.2 t)‖ ≤
      ε * ‖p.1 t - p.2 t‖ :=
    @hW (p.1 t, p.2 t) ⟨(hmem p.1 hp.1 t).2, (hmem p.2 hp.2 t).2⟩
  exact hb.trans
    (mul_le_mul_of_nonneg_left ((p.1 - p.2).norm_coe_le_norm t) hε.le)

end Hindman168
