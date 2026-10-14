import Hindman168.NativeLieShiftedExponential

/-! A genuine local logarithm near each original exponential value. It is
constructed from the actual shifted coordinate inverse. Its values lie
near the chosen original vector, and both inverse laws hold locally. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieExponentialRelativeChart (v : E) (g : G) : E :=
  extChartAt I (1 : G) ((nativeLieExponential (I := I) (G := G) v)⁻¹ * g)

 theorem nativeLieExponentialRelativeChart_self (v : E) :
    nativeLieExponentialRelativeChart (I := I) (G := G) v
      (nativeLieExponential (I := I) (G := G) v) = extChartAt I (1 : G) (1 : G) := by
  simp only [nativeLieExponentialRelativeChart, inv_mul_cancel]

 theorem nativeLieExponentialRelativeChart_contMDiffAt (v : E) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (nativeLieExponentialRelativeChart (I := I) (G := G) v)
      (nativeLieExponential (I := I) (G := G) v) := by
  have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (1 : G))
      ((nativeLieExponential (I := I) (G := G) v)⁻¹ * nativeLieExponential (I := I) (G := G) v) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_extChartAt
  exact hc.comp _ (contMDiff_mul_left : ContMDiff I I ∞
    (fun g : G => (nativeLieExponential (I := I) (G := G) v)⁻¹ * g)).contMDiffAt

 theorem nativeLieExponentialRelativeChart_exponential (v z : E) :
    nativeLieExponentialRelativeChart (I := I) (G := G) v
      (nativeLieExponential (I := I) (G := G) z) =
        nativeLieShiftedExponential (I := I) (G := G) v (z - v) := by
  unfold nativeLieShiftedExponential nativeLieRelativeCoordinateCurve
  rw [nativeLieRelativeCurve_time_one]
  have h : v + (z - v) = z := by abel
  rw [h]
  rfl

variable [Group.IsNilpotent G]

noncomputable def nativeLieExponentialLocalLogAt (v : E) (g : G) : E :=
  v + nativeLieShiftedExponentialInverse (I := I) (G := G) v
    (nativeLieExponentialRelativeChart (I := I) (G := G) v g)

 theorem nativeLieExponentialLocalLogAt_self (v : E) :
    nativeLieExponentialLocalLogAt (I := I) (G := G) v
      (nativeLieExponential (I := I) (G := G) v) = v := by
  simp only [nativeLieExponentialLocalLogAt, nativeLieExponentialRelativeChart_self,
    nativeLieShiftedExponentialInverse_center, add_zero]

 theorem nativeLieExponentialLocalLogAt_contMDiffAt (v : E) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (nativeLieExponentialLocalLogAt (I := I) (G := G) v)
      (nativeLieExponential (I := I) (G := G) v) := by
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (nativeLieShiftedExponentialInverse (I := I) (G := G) v)
      (nativeLieExponentialRelativeChart (I := I) (G := G) v
        (nativeLieExponential (I := I) (G := G) v)) := by
    rw [nativeLieExponentialRelativeChart_self]
    exact (nativeLieShiftedExponentialInverse_contDiffAt v).contMDiffAt
  exact contMDiffAt_const.add (hi.comp _ (nativeLieExponentialRelativeChart_contMDiffAt v))

 theorem nativeLieExponentialLocalLogAt_left (v : E) :
    ∀ᶠ z : E in 𝓝 v, nativeLieExponentialLocalLogAt (I := I) (G := G) v
      (nativeLieExponential (I := I) (G := G) z) = z := by
  have ht : Tendsto (fun z : E => z - v) (𝓝 v) (𝓝 0) := by
    have h : ContinuousAt (fun z : E => z - v) v := (continuous_id.sub continuous_const).continuousAt
    have h' : Tendsto (fun z : E => z - v) (𝓝 v) (𝓝 (v - v)) := h.tendsto
    simpa only [sub_self] using h'
  have he := ht.eventually (nativeLieShiftedExponentialInverse_left (I := I) (G := G) v)
  filter_upwards [he] with z hz
  unfold nativeLieExponentialLocalLogAt
  rw [nativeLieExponentialRelativeChart_exponential, hz]
  abel

 theorem nativeLieExponentialLocalLogAt_right (v : E) :
    ∀ᶠ g : G in 𝓝 (nativeLieExponential (I := I) (G := G) v),
      nativeLieExponential (E := E) (I := I) (G := G)
        (nativeLieExponentialLocalLogAt (E := E) (I := I) (G := G) v g) = g := by
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  let log : G → E := nativeLieExponentialLocalLogAt (I := I) (G := G) v
  have hc := (nativeLieExponentialRelativeChart_contMDiffAt (I := I) (G := G) v).continuousAt.tendsto
  rw [nativeLieExponentialRelativeChart_self] at hc
  have he := hc.eventually (nativeLieShiftedExponentialInverse_right (I := I) (G := G) v)
  have hlog : ContinuousAt log (exp v) := (nativeLieExponentialLocalLogAt_contMDiffAt v).continuousAt
  have hexp : Continuous exp := (nativeLieExponential_contMDiff (I := I) (G := G)).continuous
  have hr : Continuous (fun g : G => (exp v)⁻¹ * g) :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun g : G => (exp v)⁻¹ * g)).continuous
  have hr0 : Tendsto (fun g : G => (exp v)⁻¹ * g) (𝓝 (exp v)) (𝓝 1) := by
    simpa only [inv_mul_cancel] using hr.continuousAt.tendsto (x := exp v)
  have ht0 : Tendsto (fun g : G => (exp v)⁻¹ * exp (log g)) (𝓝 (exp v)) (𝓝 1) := by
    have h := (hr.continuousAt.comp (hexp.continuousAt.comp hlog)).tendsto
    change Tendsto (fun g : G => (exp v)⁻¹ * exp (log g)) (𝓝 (exp v))
      (𝓝 ((exp v)⁻¹ * exp (log (exp v)))) at h
    have hv : log (exp v) = v := nativeLieExponentialLocalLogAt_self v
    rw [hv, inv_mul_cancel] at h
    exact h
  have hs := hr0.eventually (extChartAt_source_mem_nhds (I := I) (1 : G))
  have hs' := ht0.eventually (extChartAt_source_mem_nhds (I := I) (1 : G))
  filter_upwards [he, hs, hs'] with g hg hsrc hsrc'
  have hchart : extChartAt I (1 : G) ((exp v)⁻¹ * exp (log g)) =
      extChartAt I (1 : G) ((exp v)⁻¹ * g) := by
    unfold nativeLieShiftedExponential nativeLieRelativeCoordinateCurve at hg
    rw [nativeLieRelativeCurve_time_one] at hg
    exact hg
  exact mul_left_cancel ((extChartAt I (1 : G)).injOn hsrc' hsrc hchart)

end Hindman168
