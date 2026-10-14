import Hindman168.NativeLieExponentialDerivative

/-! A local logarithm for the original native Lie group, constructed
from the proved strict exponential derivative and the actual chart.
Both local inverse laws and its native derivative are established. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G] [T2Space G]

 noncomputable def nativeLieLocalLogarithm (g : G) : E :=
  nativeLieExponentialCoordinateInverse (E := E) (I := I) (G := G) (extChartAt I (1 : G) g)

 theorem nativeLieLocalLogarithm_one :
    nativeLieLocalLogarithm (E := E) (I := I) (G := G) (1 : G) = (0 : E) := by
  have h := (nativeLieExponentialCoordinateInverse_left (I := I) (G := G)).self_of_nhds
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  rw [hz] at h
  exact h

 theorem nativeLieLocalLogarithm_continuousAt_one :
    ContinuousAt (nativeLieLocalLogarithm (E := E) (I := I) (G := G) : G → E) (1 : G) := by
  exact (nativeLieExponentialCoordinateInverse_hasStrictFDerivAt (I := I) (G := G)).continuousAt.comp
    (f := extChartAt I (1 : G)) (continuousAt_extChartAt (1 : G))

 theorem nativeLieLocalLogarithm_eventually_left :
    ∀ᶠ v : E in 𝓝 0, nativeLieLocalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) v) = v :=
  nativeLieExponentialCoordinateInverse_left (I := I) (G := G)

 theorem nativeLieLocalLogarithm_eventually_right :
    ∀ᶠ g : G in 𝓝 1, nativeLieExponential (I := I) (G := G)
      (nativeLieLocalLogarithm (E := E) (I := I) (G := G) g) = g := by
  have hχ : ContinuousAt (extChartAt I (1 : G)) (1 : G) := continuousAt_extChartAt _
  have he := hχ.tendsto.eventually
    (nativeLieExponentialCoordinateInverse_right (I := I) (G := G))
  have hc := (nativeLieExponential_continuous (I := I) (G := G)).continuousAt.comp
    (f := (nativeLieLocalLogarithm (E := E) (I := I) (G := G) : G → E))
    (nativeLieLocalLogarithm_continuousAt_one (I := I) (G := G))
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  have ht := hc.tendsto
  rw [Function.comp_apply, nativeLieLocalLogarithm_one, hz] at ht
  have hs := ht.eventually (extChartAt_source_mem_nhds (I := I) (1 : G))
  filter_upwards [he, hs, extChartAt_source_mem_nhds (I := I) (1 : G)] with g hg hsg hsrc
  have h := congrArg ((extChartAt I (1 : G)).symm) hg
  change (extChartAt I (1 : G)).symm (extChartAt I (1 : G)
    (nativeLieExponential (I := I) (G := G) (nativeLieLocalLogarithm (E := E) (I := I) (G := G) g))) =
      (extChartAt I (1 : G)).symm (extChartAt I (1 : G) g) at h
  exact ((extChartAt I (1 : G)).left_inv hsg).symm.trans
    (h.trans ((extChartAt I (1 : G)).left_inv hsrc))

 theorem nativeLieLocalLogarithm_hasMFDerivAt_one :
    HasMFDerivAt I 𝓘(ℝ, E) (nativeLieLocalLogarithm (E := E) (I := I) (G := G) : G → E) (1 : G)
      (ContinuousLinearMap.id ℝ E) := by
  have hc := (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (1 : G))).hasMFDerivAt
  rw [mfderiv_extChartAt_self] at hc
  have hd := (nativeLieExponentialCoordinateInverse_hasStrictFDerivAt (I := I) (G := G)).hasFDerivAt.hasMFDerivAt
  have h := hd.comp (1 : G) hc
  apply h.congr_mfderiv
  change (ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E) = _
  exact ContinuousLinearMap.comp_id _

 theorem nativeLieLocalLogarithm_mfderiv_one :
    mfderiv I 𝓘(ℝ, E) (nativeLieLocalLogarithm (E := E) (I := I) (G := G) : G → E) (1 : G) =
      ContinuousLinearMap.id ℝ E :=
  (nativeLieLocalLogarithm_hasMFDerivAt_one (I := I) (G := G)).mfderiv

 theorem nativeLieExponential_locally_injective :
    ∃ U : Set E, U ∈ 𝓝 0 ∧
      InjOn (fun v : E => nativeLieExponential (I := I) (G := G) v) U := by
  refine ⟨{v : E | nativeLieLocalLogarithm (E := E) (I := I) (G := G)
    (nativeLieExponential (I := I) (G := G) v) = v},
    nativeLieLocalLogarithm_eventually_left (I := I) (G := G), ?_⟩
  intro x hx y hy hxy
  exact hx.symm.trans ((congrArg (nativeLieLocalLogarithm (E := E) (I := I) (G := G)) hxy).trans hy)

 theorem nativeLieExponential_image_mem_nhds {U : Set E} (hU : U ∈ 𝓝 0) :
    (fun v : E => nativeLieExponential (I := I) (G := G) v) '' U ∈ 𝓝 (1 : G) := by
  have ht := (nativeLieLocalLogarithm_continuousAt_one (I := I) (G := G)).tendsto
  rw [nativeLieLocalLogarithm_one] at ht
  have hpre := ht.eventually hU
  filter_upwards [hpre, nativeLieLocalLogarithm_eventually_right (I := I) (G := G)] with g hg he
  exact ⟨nativeLieLocalLogarithm (E := E) (I := I) (G := G) g, hg, he⟩

end Hindman168
