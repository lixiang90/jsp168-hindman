import Hindman168.LieCoordinateFlowControl
import Hindman168.LieExponentialContinuity

/-! Transport of the actual controlled coordinate flow through the
original inverse chart. Native integral-curve uniqueness identifies it
with the retained native one-parameter curves on a common interval. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G]

 omit [CompleteSpace E] [BoundarylessManifold I G] in
 theorem lie_coordinate_curve_transport {f : ℝ → E} {s : Set ℝ} (v : E)
    (hf : ∀ t ∈ s, HasDerivAt f
      (lieInvariantCoordinateField (I := I) (G := G) (v, f t)) t)
    (hchart : ∀ t ∈ s, f t ∈ interior (extChartAt I (1 : G)).target) :
    IsMIntegralCurveOn ((extChartAt I (1 : G)).symm ∘ f)
      (mulInvariantVectorField (I := I) v) s := by
  intro t ht
  let xₜ : G := (extChartAt I (1 : G)).symm (f t)
  have hd : HasDerivAt f
      (tangentCoordChange I xₜ (1 : G) xₜ (mulInvariantVectorField (I := I) v xₜ)) t := hf t ht
  have hz := hchart t ht
  have hz' := interior_subset hz
  have hft1 := (extChartAt I (1 : G)).target_subset_preimage_source hz'
  have hft2 := mem_extChartAt_source (I := I) xₜ
  have hdchart : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I (1 : G)).symm) ∘ f)
      (mulInvariantVectorField (I := I) v xₜ : E) t := by
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ)
        (v := mulInvariantVectorField (I := I) v xₜ) hft2,
      ← tangentCoordChange_comp (x := (1 : G)) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ hd
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _
      (mem_nhds_iff.mpr ⟨interior (extChartAt I (1 : G)).target,
        subset_trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hz⟩)
    rw [← (extChartAt I (1 : G)).right_inv hz']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨?_, ?_⟩
  · exact (continuousAt_extChartAt_symm'' hz').comp (f := f) hd.continuousAt
  · simp only [mfld_simps]
    change HasFDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I (1 : G)).symm) ∘ f)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField (I := I) v xₜ : E)) univ t
    exact hdchart.hasFDerivAt.hasFDerivWithinAt

 noncomputable def lieIdentityCoordinateFlow (v : E) : C(Icc (-2 : ℝ) 2, E × E) :=
  lieCoordinateParametricFlow (I := I) (G := G) (by norm_num)
    ⟨0, by constructor <;> norm_num⟩ v

 theorem lieIdentityCoordinateFlow_zero :
    lieIdentityCoordinateFlow (I := I) (G := G) (0 : E) =
      ContinuousMap.const (Icc (-2 : ℝ) 2) (0, extChartAt I (1 : G) (1 : G)) :=
  lieCoordinateParametricFlow_zero (I := I) (G := G) _ _

variable [T2Space G]

 theorem lieIdentityCoordinateFlow_eventually_native :
    ∀ᶠ v : E in 𝓝 0, ∀ t ∈ Ioo (-2 : ℝ) 2,
      (extChartAt I (1 : G)).symm
        (curveClippedExtension (by norm_num)
          (lieIdentityCoordinateFlow (I := I) (G := G) v) t).2 =
        lieOneParameterCurve (I := I) (G := G) v t := by
  have hi := lieCoordinateParametricFlow_eventually_integral (I := I) (G := G)
    (show (-2 : ℝ) ≤ 2 by norm_num) ⟨0, by constructor <;> norm_num⟩
  have hc := lieCoordinateParametricFlow_eventually_chart (I := I) (G := G)
    (show (-2 : ℝ) ≤ 2 by norm_num) ⟨0, by constructor <;> norm_num⟩
  filter_upwards [hi, hc] with v hv hcv
  let α := curveClippedExtension (show (-2 : ℝ) ≤ 2 by norm_num)
    (lieIdentityCoordinateFlow (I := I) (G := G) v)
  have hfirst : ∀ t ∈ Ioo (-2 : ℝ) 2, (α t).1 = v :=
    lieCoordinateParametricFlow_frozen_first (I := I) (G := G) _ _
      (by constructor <;> norm_num) hv.1 hv.2
  have hd : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun s => (α s).2)
      (lieInvariantCoordinateField (I := I) (G := G) (v, (α t).2)) t := by
    intro t ht
    have h := (hv.2 t ht).snd
    change HasDerivAt (fun s => (α s).2)
      (lieInvariantCoordinateField (I := I) (G := G) ((α t).1, (α t).2)) t at h
    rw [hfirst t ht] at h
    exact h
  have hz : ∀ t ∈ Ioo (-2 : ℝ) 2, (α t).2 ∈
      interior (extChartAt I (1 : G)).target := by
    intro t ht
    exact hcv (projIcc (-2 : ℝ) 2 (by norm_num) t)
  have hnative := lie_coordinate_curve_transport (I := I) (G := G) v hd hz
  have hinit : ((extChartAt I (1 : G)).symm ∘ (fun s => (α s).2)) 0 =
      lieOneParameterCurve (I := I) (G := G) v 0 := by
    rw [lieOneParameterCurve_zero]
    change (extChartAt I (1 : G)).symm
      (curveClippedExtension (by norm_num)
        (lieIdentityCoordinateFlow (I := I) (G := G) v) (⟨0, by constructor <;> norm_num⟩ : Icc (-2 : ℝ) 2)).2 = 1
    rw [curveClippedExtension_of_mem]
    change (extChartAt I (1 : G)).symm
      (lieCoordinateParametricFlow (I := I) (G := G) (by norm_num)
        ⟨0, by constructor <;> norm_num⟩ v ⟨0, by constructor <;> norm_num⟩).2 = 1
    rw [hv.1]
    exact (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (I := I) (by constructor <;> norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    (lie_invariant_field_contMDiff_one v) hnative
    ((lieOneParameterCurve_integral (I := I) (G := G) v).isMIntegralCurveOn _) hinit

 theorem lieIdentityCoordinateFlow_eventually_chart_native :
    ∀ᶠ v : E in 𝓝 0, ∀ t : Icc (-2 : ℝ) 2, (t : ℝ) ∈ Ioo (-2 : ℝ) 2 →
      (lieIdentityCoordinateFlow (I := I) (G := G) v t).2 =
        extChartAt I (1 : G) (lieOneParameterCurve (I := I) (G := G) v t) := by
  have hc := lieCoordinateParametricFlow_eventually_chart (I := I) (G := G)
    (show (-2 : ℝ) ≤ 2 by norm_num) ⟨0, by constructor <;> norm_num⟩
  filter_upwards [lieIdentityCoordinateFlow_eventually_native (I := I) (G := G), hc] with v hv hcv
  intro t ht
  have he := hv t ht
  rw [curveClippedExtension_of_mem] at he
  rw [← he]
  exact ((extChartAt I (1 : G)).right_inv (interior_subset (hcv t))).symm

end Hindman168
