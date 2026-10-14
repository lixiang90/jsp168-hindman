import Hindman168.NativeLieCoordinateBracket
import Hindman168.MixedFlowJacobian

/-! The genuine native right-translation flow in the original identity
chart. Its coordinate ODE and regularity are derived from the actual native
curve, actual multiplication and actual inverse chart. -/

namespace Hindman168
open Bundle Function Set Filter Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRightCoordinateFlow (v : E) (p : ℝ × E) : E :=
  extChartAt I (1 : G) ((extChartAt I (1 : G)).symm p.2 *
    lieOneParameterCurve (I := I) (G := G) v p.1)

 theorem nativeLieRightCoordinateFlow_zero (v : E) {z : E}
    (hz : z ∈ (extChartAt I (1 : G)).target) :
    nativeLieRightCoordinateFlow (I := I) (G := G) v (0, z) = z := by
  unfold nativeLieRightCoordinateFlow
  rw [lieOneParameterCurve_zero, mul_one]
  exact (extChartAt I (1 : G)).right_inv hz

 theorem nativeLieRightCoordinateFlow_contDiffAt_identity (v : E) :
    ContDiffAt ℝ ∞ (nativeLieRightCoordinateFlow (I := I) (G := G) v)
      (0, extChartAt I (1 : G) (1 : G)) := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  have hi : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I (1 : G)).symm z₀ :=
    (contMDiffWithinAt_extChartAt_symm_range_self (n := ∞) (1 : G)).contMDiffAt
      (nativeLieIdentityChart_range_nhds (I := I) (G := G))
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun p : ℝ × E => (extChartAt I (1 : G)).symm p.2) (0, z₀) :=
    hi.comp (0, z₀) contMDiffAt_snd
  have hg : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun p : ℝ × E => lieOneParameterCurve (I := I) (G := G) v p.1) (0, z₀) :=
    (lieOneParameterCurve_joint_contMDiff (I := I) (G := G)).contMDiffAt.comp (0, z₀)
      (contMDiffAt_const.prodMk contMDiffAt_fst)
  have hm := hs.mul hg
  have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (1 : G))
      ((extChartAt I (1 : G)).symm z₀ * lieOneParameterCurve (I := I) (G := G) v 0) := by
    simpa only [z₀, lieOneParameterCurve_zero, mul_one,
      (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))]
      using (contMDiffAt_extChartAt (I := I) (n := ∞) (x := (1 : G)))
  have h := hc.comp (0, z₀) hm
  rw [← modelWithCornersSelf_prod] at h
  rw [chartedSpaceSelf_prod] at h
  convert! h.contDiffAt using 1

 theorem nativeLieRightCoordinateFlow_hasDerivAt (v : E) (z : E) (t : ℝ)
    (hchart : (extChartAt I (1 : G)).symm z * lieOneParameterCurve (I := I) (G := G) v t ∈
      (chartAt H (1 : G)).source) :
    HasDerivAt (fun s : ℝ => nativeLieRightCoordinateFlow (I := I) (G := G) v (s, z))
      (nativeLieCoordinateVectorField (I := I) (G := G) v
        (nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z))) t := by
  let x := (extChartAt I (1 : G)).symm z * lieOneParameterCurve (I := I) (G := G) v t
  have hi := lie_invariant_integralCurve_left_translate (I := I) v
    (lieOneParameterCurve_integral (I := I) (G := G) v) ((extChartAt I (1 : G)).symm z) t
  have hc := (mdifferentiableAt_extChartAt (I := I) hchart).hasMFDerivAt.comp t hi
  have hfd : HasFDerivAt
      (fun s : ℝ => nativeLieRightCoordinateFlow (I := I) (G := G) v (s, z))
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) x).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField (I := I) (G := G) v x : E))) t := by
    convert! hc.hasFDerivAt using 1
  have hx : x ∈ (extChartAt I (1 : G)).source := by
    rwa [extChartAt_source (I := I)]
  have hz : nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z) ∈
      (extChartAt I (1 : G)).target := (extChartAt I (1 : G)).map_source hx
  have he := nativeLieCoordinateVectorField_eq_chart_derivative (I := I) (G := G) v hz
  have hinv : (extChartAt I (1 : G)).symm
      (nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z)) = x :=
    (extChartAt I (1 : G)).left_inv hx
  have hv : mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) x
      (mulInvariantVectorField (I := I) (G := G) v x) =
      nativeLieCoordinateVectorField (I := I) (G := G) v
        (nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z)) := by
    rw [he]
    congr 2 <;> exact hinv.symm
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hfd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro a
  change mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) x
      (a • mulInvariantVectorField (I := I) (G := G) v x) =
    a • nativeLieCoordinateVectorField (I := I) (G := G) v
      (nativeLieRightCoordinateFlow (I := I) (G := G) v (t, z))
  rw [map_smul, hv]
  rfl

 theorem nativeLieRightCoordinateFlow_time_derivative_eventually (v : E) :
    ∀ᶠ z : E in 𝓝 (extChartAt I (1 : G) (1 : G)),
      fderiv ℝ (nativeLieRightCoordinateFlow (I := I) (G := G) v) (0, z) (1, 0) =
        nativeLieCoordinateVectorField (I := I) (G := G) v z := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  have hf := (nativeLieRightCoordinateFlow_contDiffAt_identity (I := I) (G := G) v).of_le
    (show (1 : ℕ∞ω) ≤ ∞ from by norm_num)
  have he := hf.eventually (by norm_num : (1 : ℕ∞ω) ≠ ∞)
  have hi : ContinuousAt (fun z : E => ((0 : ℝ), z)) z₀ :=
    continuousAt_const.prodMk continuousAt_id
  have hdnear := hi.eventually he
  filter_upwards [nativeLieIdentityChart_target_nhds (I := I) (G := G), hdnear] with z hz hdz
  have hchart : (extChartAt I (1 : G)).symm z * lieOneParameterCurve (I := I) (G := G) v 0 ∈
      (chartAt H (1 : G)).source := by
    simp only [lieOneParameterCurve_zero, mul_one]
    have h := (extChartAt I (1 : G)).map_target hz
    rwa [extChartAt_source (I := I)] at h
  have hv := nativeLieRightCoordinateFlow_hasDerivAt (I := I) (G := G) v z 0 hchart
  rw [nativeLieRightCoordinateFlow_zero v hz] at hv
  have hd := (hdz.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 z))
  exact hd.unique hv

 theorem nativeLieRightCoordinateFlow_jacobian_hasDerivAt (v w : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ (nativeLieRightCoordinateFlow (I := I) (G := G) v)
      (t, extChartAt I (1 : G) (1 : G)) (0, w))
      (fderiv ℝ (nativeLieCoordinateVectorField (I := I) (G := G) v)
        (extChartAt I (1 : G) (1 : G)) w) 0 :=
  mixedFlowJacobian_hasDerivAt
    ((nativeLieRightCoordinateFlow_contDiffAt_identity (I := I) (G := G) v).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (nativeLieRightCoordinateFlow_time_derivative_eventually v) w

end Hindman168
