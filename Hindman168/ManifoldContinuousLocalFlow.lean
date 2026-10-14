import Hindman168.ODEContinuousLocalFlow
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! Continuous local flows in the original manifold topology. The
coordinate ODE flow is constructed, restricted to a common chart
neighbourhood, and transported using actual chart derivatives. -/

namespace Hindman168
open Function Manifold Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M]

 theorem manifold_contMDiffAt_exists_continuous_local_flow
    {v : (x : M) → TangentSpace I x} {x₀ : M}
    (hv : ContMDiffAt I I.tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) (t₀ : ℝ) :
    ∃ U : Set M, U ∈ 𝓝 x₀ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ γ : M × ℝ → M,
      (∀ x ∈ U, γ (x, t₀) = x ∧
        IsMIntegralCurveOn (fun t => γ (x, t)) v (Ioo (t₀ - ε) (t₀ + ε))) ∧
      ContinuousOn γ (U ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  let f : E → E := fun z =>
    tangentCoordChange I ((extChartAt I x₀).symm z) x₀
      ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))
  have hx : I.IsInteriorPoint x₀ := BoundarylessManifold.isInteriorPoint
  rw [contMDiffAt_iff] at hv
  have hf : ContDiffAt ℝ 1 f (extChartAt I x₀ x₀) :=
    (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  obtain ⟨r, hr, ε, hε, α, hα, hc⟩ :=
    contDiffAt_exists_continuous_local_flow_mem hf t₀
      (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx))
  let U := (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' Metric.ball
    (extChartAt I x₀ x₀) r
  have hU : U ∈ 𝓝 x₀ := Filter.inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  let γ : M × ℝ → M := fun p => (extChartAt I x₀).symm (α (extChartAt I x₀ p.1, p.2))
  refine ⟨U, hU, ε, hε, γ, ?_, ?_⟩
  · intro x hxU
    have hxx := hxU.2
    refine ⟨?_, fun t ht => ?_⟩
    · change (extChartAt I x₀).symm (α (extChartAt I x₀ x, t₀)) = x
      rw [(hα _ hxx).1]
      exact (extChartAt I x₀).left_inv hxU.1
    · let z := α (extChartAt I x₀ x, t)
      let xₜ : M := (extChartAt I x₀).symm z
      have hd : HasDerivAt (fun u => α (extChartAt I x₀ x, u))
          (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) t := (hα _ hxx).2 t ht |>.1
      have hz : z ∈ interior (extChartAt I x₀).target := (hα _ hxx).2 t ht |>.2
      have hz' := interior_subset hz
      have hft1 := (extChartAt I x₀).target_subset_preimage_source hz'
      have hft2 := mem_extChartAt_source (I := I) xₜ
      have hdchart : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘
          (fun u => α (extChartAt I x₀ x, u))) (v xₜ : E) t := by
        rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ)
            (v := v xₜ) hft2,
          ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
        apply HasFDerivAt.comp_hasDerivAt _ _ hd
        apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
          (mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
            subset_trans interior_subset (extChartAt_target_subset_range ..),
            isOpen_interior, hz⟩)
        rw [← (extChartAt I x₀).right_inv hz']
        exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
      apply HasMFDerivAt.hasMFDerivWithinAt
      refine ⟨?_, ?_⟩
      · change ContinuousAt ((extChartAt I x₀).symm ∘
          (fun u => α (extChartAt I x₀ x, u))) t
        exact (continuousAt_extChartAt_symm'' hz').comp
          (f := fun u => α (extChartAt I x₀ x, u)) hd.continuousAt
      · simp only [mfld_simps]
        change HasFDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘
          (fun u => α (extChartAt I x₀ x, u)))
          ((1 : ℝ →L[ℝ] ℝ).smulRight (v xₜ : E)) univ t
        exact hdchart.hasFDerivAt.hasFDerivWithinAt
  · have hχ : ContinuousOn (fun p : M × ℝ => (extChartAt I x₀ p.1, p.2))
        (U ×ˢ Ioo (t₀ - ε) (t₀ + ε)) :=
      ((continuousOn_extChartAt x₀).comp continuousOn_fst
        (fun p hp => hp.1.1)).prodMk continuousOn_snd
    have hmap : MapsTo (fun p : M × ℝ => (extChartAt I x₀ p.1, p.2))
        (U ×ˢ Ioo (t₀ - ε) (t₀ + ε))
        (Metric.ball (extChartAt I x₀ x₀) r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) :=
      fun p hp => ⟨hp.1.2, hp.2⟩
    exact (continuousOn_extChartAt_symm x₀).comp (hc.comp hχ hmap)
      (fun p hp => interior_subset ((hα _ hp.1.2).2 p.2 hp.2).2)

end Hindman168
