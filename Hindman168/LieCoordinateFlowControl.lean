import Hindman168.LieCoordinateParametricFlow
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform chart control and constancy of the frozen parameter for the
actual implicit coordinate flow. These conclusions are derived from
its proved curve-space continuity and its genuine differential equation. -/

namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 theorem lieCoordinateParametricFlow_continuousAt_zero :
    ContinuousAt (lieCoordinateParametricFlow (I := I) (G := G) hab t₀) (0 : E) := by
  exact (curvePicardImplicit_hasStrictFDerivAt hab t₀
    (lieFrozenCoordinateField_hasStrictFDerivAt (I := I) (G := G))
    (lieFrozenCoordinateLinearization_square_zero (E := E))).continuousAt.comp
      (f := fun v : E => (v, extChartAt I (1 : G) (1 : G)))
      (continuous_id.prodMk continuous_const).continuousAt

 theorem lieCoordinateParametricFlow_eventually_chart :
    ∀ᶠ v : E in 𝓝 0, ∀ t : Icc a b,
      (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t).2 ∈
        interior (extChartAt I (1 : G)).target := by
  let z₀ := extChartAt I (1 : G) (1 : G)
  have hz : z₀ ∈ interior (extChartAt I (1 : G)).target :=
    (I.isInteriorPoint_iff).mp (BoundarylessManifold.isInteriorPoint (I := I) (x := (1 : G)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
  have hc := lieCoordinateParametricFlow_continuousAt_zero (I := I) (G := G) hab t₀
  have he := hc.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  rw [lieCoordinateParametricFlow_zero] at he
  filter_upwards [he] with v hv
  intro t
  apply hball
  change dist (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t).2 z₀ < r
  have hd := ContinuousMap.dist_apply_le_dist
    (f := lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v)
    (g := ContinuousMap.const (Icc a b) (0, z₀)) t
  change dist (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v)
    (ContinuousMap.const (Icc a b) (0, z₀)) < r at hv
  exact lt_of_le_of_lt (le_trans (le_max_right _ _) hd) hv

 theorem lieCoordinateParametricFlow_frozen_first {v : E}
    (ht₀ : (t₀ : ℝ) ∈ Ioo a b)
    (hinit : lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t₀ =
      (v, extChartAt I (1 : G) (1 : G)))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt
      (curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v))
      (lieFrozenCoordinateField (I := I) (G := G)
        (curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v) t)) t) :
    ∀ t ∈ Ioo a b,
      (curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v) t).1 = v := by
  let α := curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => (α s).1) (0 : E) t :=
    (hode t ht).fst
  intro t ht
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) ht ht₀
  change (α t).1 = v
  rw [he]
  change (curveClippedExtension hab
    (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v) t₀).1 = v
  rw [curveClippedExtension_of_mem, hinit]

end Hindman168
