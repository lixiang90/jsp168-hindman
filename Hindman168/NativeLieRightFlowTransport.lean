import Hindman168.NativeLieRightCoordinateFlow

/-! The actual spatial derivative of the original coordinate flow transports
the actual adjoint action to the original invariant coordinate field. -/

namespace Hindman168
open Bundle Function Set Filter Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieRightCoordinateFlow_identity_state (v : E) (t : ℝ) :
    nativeLieRightCoordinateFlow (I := I) (G := G) v
      (t, extChartAt I (1 : G) (1 : G)) =
      extChartAt I (1 : G) (lieOneParameterCurve (I := I) (G := G) v t) := by
  unfold nativeLieRightCoordinateFlow
  rw [(extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G)), one_mul]

omit [CompleteSpace E] [T2Space G] in
 theorem nativeLieIdentityChart_inverse_mfderiv :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm
      (extChartAt I (1 : G) (1 : G)) : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  rw [← mfderivWithin_of_mem_nhds (nativeLieIdentityChart_range_nhds (I := I) (G := G))]
  exact mfderivWithin_range_extChartAt_symm

 theorem nativeLieRightCoordinateFlow_state_hasFDerivAt (v : E) (t : ℝ)
    (ht : lieOneParameterCurve (I := I) (G := G) v t ∈ (chartAt H (1 : G)).source) :
    HasFDerivAt (fun z : E => nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z))
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G))
          (lieOneParameterCurve (I := I) (G := G) v t) : E →L[ℝ] E).comp
        (mfderiv I I (fun x : G => x * lieOneParameterCurve (I := I) (G := G) v t) 1))
      (extChartAt I (1 : G) (1 : G)) := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  let g := lieOneParameterCurve (I := I) (G := G) v t
  have hi := (mdifferentiableWithinAt_extChartAt_symm (I := I)
    (mem_extChartAt_target (I := I) (1 : G))).mdifferentiableAt
      (nativeLieIdentityChart_range_nhds (I := I) (G := G))
  have hr := (nativeLieRightTranslation_contMDiff (I := I) g).mdifferentiable
    (by norm_num)
  have hs : (extChartAt I (1 : G)).symm z₀ = 1 :=
    (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))
  have hpoint : (extChartAt I (1 : G)).symm z₀ * g ∈ (chartAt H (1 : G)).source := by
    rw [hs, one_mul]
    exact ht
  have hc := (mdifferentiableAt_extChartAt (I := I) hpoint).hasMFDerivAt.comp z₀
    ((hr ((extChartAt I (1 : G)).symm z₀)).hasMFDerivAt.comp z₀ hi.hasMFDerivAt)
  erw [hs, one_mul] at hc
  have hfd : HasFDerivAt
      (fun z : E => nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z))
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G))
          g : E →L[ℝ] E).comp
        (mfderiv I I (fun x : G => x * g) 1)).comp
          (mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm z₀)) z₀ := by
    convert! hc.hasFDerivAt using 1
  apply hfd.congr_fderiv
  rw [nativeLieIdentityChart_inverse_mfderiv]
  apply ContinuousLinearMap.ext
  intro w
  rfl

 theorem nativeLieRightCoordinateFlow_transport_eventually (v w : E) :
    ∀ᶠ t : ℝ in 𝓝 0,
      fderiv ℝ (nativeLieRightCoordinateFlow (I := I) (G := G) v)
          (t, extChartAt I (1 : G) (1 : G))
          (0, nativeLieAdjointCurve (I := I) (G := G) v t w) =
        nativeLieCoordinateVectorField (I := I) (G := G) w
          (nativeLieRightCoordinateFlow (I := I) (G := G) v
            (t, extChartAt I (1 : G) (1 : G))) := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  let F := nativeLieRightCoordinateFlow (I := I) (G := G) v
  have hf := (nativeLieRightCoordinateFlow_contDiffAt_identity (I := I) (G := G) v).of_le
    (show (1 : ℕ∞ω) ≤ ∞ from by norm_num)
  have hp : ContinuousAt (fun t : ℝ => (t, z₀)) 0 := continuousAt_id.prodMk continuousAt_const
  have hdiff := hp.eventually (hf.eventually (by norm_num : (1 : ℕ∞ω) ≠ ∞))
  have hsource : ∀ᶠ t : ℝ in 𝓝 0,
      lieOneParameterCurve (I := I) (G := G) v t ∈ (chartAt H (1 : G)).source := by
    have hn : (chartAt H (1 : G)).source ∈ 𝓝 (lieOneParameterCurve (I := I) (G := G) v 0) := by
      rw [lieOneParameterCurve_zero]
      exact (chartAt H (1 : G)).open_source.mem_nhds (mem_chart_source H (1 : G))
    exact (lieOneParameterCurve_continuous (I := I) (G := G) v).continuousAt.preimage_mem_nhds hn
  filter_upwards [hdiff, hsource] with t hdt ht
  let g := lieOneParameterCurve (I := I) (G := G) v t
  have hstate := nativeLieRightCoordinateFlow_state_hasFDerivAt (I := I) (G := G) v t ht
  have hchain := hdt.differentiableAt (by norm_num) |>.hasFDerivAt.comp z₀
    ((hasFDerivAt_const t z₀).prodMk (hasFDerivAt_id z₀))
  have he := hchain.unique hstate
  have hew := congrArg (fun L : E →L[ℝ] E => L (nativeLieAdjoint (I := I) g w)) he
  have hg : g ∈ (extChartAt I (1 : G)).source := by
    rwa [extChartAt_source (I := I)]
  have hfield := nativeLieCoordinateVectorField_eq_chart_derivative (I := I) (G := G) w
    ((extChartAt I (1 : G)).map_source hg)
  have hright := nativeLieRightTranslation_invariant_field (I := I) g 1 w
  erw [lie_invariant_field_one] at hright
  have hright' : mfderiv I I (fun x : G => x * g) 1 (nativeLieAdjoint (I := I) g w) =
      mulInvariantVectorField (I := I) (G := G) w g := by
    convert! hright using 1
    congr 1
    exact (one_mul g).symm
  change fderiv ℝ F (t, z₀) (0, nativeLieAdjoint (I := I) g w) =
    nativeLieCoordinateVectorField (I := I) (G := G) w (F (t, z₀))
  have hF : F (t, z₀) = extChartAt I (1 : G) g :=
    nativeLieRightCoordinateFlow_identity_state v t
  rw [hF, hfield]
  have hinv : (extChartAt I (1 : G)).symm (extChartAt I (1 : G) g) = g :=
    (extChartAt I (1 : G)).left_inv hg
  convert! hew using 1
  change mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm (extChartAt I (1 : G) g))
      (mulInvariantVectorField (I := I) (G := G) w ((extChartAt I (1 : G)).symm (extChartAt I (1 : G) g))) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) g
        (mfderiv I I (fun x : G => x * g) 1 (nativeLieAdjoint (I := I) g w))
  rw [hright']
  congr 2

end Hindman168
