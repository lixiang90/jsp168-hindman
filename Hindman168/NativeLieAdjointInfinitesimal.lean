import Hindman168.NativeLieRightFlowTransport
import Hindman168.NativeLieAdjointExponential

/-! Identify the derivative of the genuine adjoint curve with the original
native Lie bracket. The proof differentiates the proved transport identity
for the actual right-translation flow in the original identity chart. -/

namespace Hindman168
open Bundle Function Set Filter Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieRightCoordinateFlow_state_derivative_zero (v w : E) :
    fderiv ℝ (nativeLieRightCoordinateFlow (I := I) (G := G) v)
      (0, extChartAt I (1 : G) (1 : G)) (0, w) = w := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  let F := nativeLieRightCoordinateFlow (I := I) (G := G) v
  have hf := (nativeLieRightCoordinateFlow_contDiffAt_identity (I := I) (G := G) v).differentiableAt
    (by norm_num)
  have hc := hf.hasFDerivAt.comp z₀
    ((hasFDerivAt_const (0 : ℝ) z₀).prodMk (hasFDerivAt_id z₀))
  have he : (fun z : E => F (0, z)) =ᶠ[𝓝 z₀] (fun z => z) := by
    filter_upwards [nativeLieIdentityChart_target_nhds (I := I) (G := G)] with z hz
    exact nativeLieRightCoordinateFlow_zero v hz
  have hi : HasFDerivAt (fun z : E => F (0, z)) (ContinuousLinearMap.id ℝ E) z₀ :=
    (hasFDerivAt_id (𝕜 := ℝ) z₀).congr_of_eventuallyEq he
  have h := congrArg (fun L : E →L[ℝ] E => L w) (hc.unique hi)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using h

 theorem nativeLieAdjointGenerator_eq_coordinate_bracket (v w : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v w =
      fderiv ℝ (nativeLieCoordinateVectorField (I := I) (G := G) w)
          (extChartAt I (1 : G) (1 : G)) v -
        fderiv ℝ (nativeLieCoordinateVectorField (I := I) (G := G) v)
          (extChartAt I (1 : G) (1 : G)) w := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  let F := nativeLieRightCoordinateFlow (I := I) (G := G) v
  let V := nativeLieCoordinateVectorField (I := I) (G := G) v
  let W := nativeLieCoordinateVectorField (I := I) (G := G) w
  let A := nativeLieAdjointCurve (I := I) (G := G) v
  let B := nativeLieAdjointGenerator (I := I) (G := G) v
  let D := fderiv ℝ F
  let DD := fderiv ℝ D (0, z₀)
  have hf2 := (nativeLieRightCoordinateFlow_contDiffAt_identity (I := I) (G := G) v).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hD : HasFDerivAt D DD (0, z₀) :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have ht := hD.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 z₀))
  have htw := ht.clm_apply (hasDerivAt_const (0 : ℝ) (0, w))
  have hfirst : DD (1, 0) (0, w) = fderiv ℝ V z₀ w := by
    have h := htw.unique (nativeLieRightCoordinateFlow_jacobian_hasDerivAt
      (I := I) (G := G) v w)
    simpa only [map_zero, add_zero] using h
  have hA : HasDerivAt (fun t : ℝ => A t w) (B w) 0 :=
    nativeLieAdjointCurve_action_hasDerivAt_zero v w
  have hl := ht.clm_apply ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hA)
  have hl' : HasDerivAt (fun t : ℝ => D (t, z₀) (0, A t w))
      (fderiv ℝ V z₀ w + B w) 0 := by
    change HasDerivAt (fun t : ℝ => D (t, z₀) (0, A t w))
      (DD (1, 0) (0, A 0 w) + D (0, z₀) (0, B w)) 0 at hl
    have hzero : D (0, z₀) (0, B w) = B w := nativeLieRightCoordinateFlow_state_derivative_zero v (B w)
    simp only [A, nativeLieAdjointCurve_zero, one_apply_eq_self] at hl
    rw [hfirst, hzero] at hl
    exact hl
  have hz : z₀ ∈ (extChartAt I (1 : G)).target := mem_extChartAt_target (I := I) (1 : G)
  have hF : F (0, z₀) = z₀ := nativeLieRightCoordinateFlow_zero v hz
  have hsource : (extChartAt I (1 : G)).symm z₀ *
      lieOneParameterCurve (I := I) (G := G) v 0 ∈ (chartAt H (1 : G)).source := by
    rw [lieOneParameterCurve_zero, mul_one,
      (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))]
    exact mem_chart_source H (1 : G)
  have hflow : HasDerivAt (fun t : ℝ => F (t, z₀)) v 0 := by
    have h := nativeLieRightCoordinateFlow_hasDerivAt (I := I) (G := G) v z₀ 0 hsource
    change HasDerivAt (fun t : ℝ => F (t, z₀)) (V (F (0, z₀))) 0 at h
    have hV : V z₀ = v := nativeLieCoordinateVectorField_identity v
    rw [hF, hV] at h
    exact h
  have hW : HasFDerivAt W (fderiv ℝ W z₀) (F (0, z₀)) := by
    rw [hF]
    exact (nativeLieCoordinateVectorField_contDiffAt_identity (I := I) (G := G) w).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hr := hW.comp_hasDerivAt 0 hflow
  have he : (fun t : ℝ => W (F (t, z₀))) =ᶠ[𝓝 0]
      (fun t => D (t, z₀) (0, A t w)) := by
    filter_upwards [nativeLieRightCoordinateFlow_transport_eventually
      (I := I) (G := G) v w] with t h
    exact h.symm
  have h := (hl'.congr_of_eventuallyEq he).unique hr
  change B w = fderiv ℝ W z₀ v - fderiv ℝ V z₀ w
  exact eq_sub_of_add_eq (by simpa only [add_comm] using h)

 theorem nativeLieAdjointGenerator_eq_native_bracket (v w : GroupLieAlgebra I G) :
    nativeLieAdjointGenerator (I := I) (G := G) v w = (⁅v, w⁆ : GroupLieAlgebra I G) := by
  rw [nativeLieBracket_eq_coordinate_derivatives]
  exact nativeLieAdjointGenerator_eq_coordinate_bracket (I := I) (G := G) v w

end Hindman168
