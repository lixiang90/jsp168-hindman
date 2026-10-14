import Hindman168.CurvePicardSmooth
import Hindman168.LieInvariantFieldSmooth
import Hindman168.NativeLieLocalLogarithm

/-! Actual smoothness at zero of the original native exponential and
of its retained local logarithm at the group identity. The original
coordinate flow and its native uniqueness identification are reused;
no flow regularity or exponential smoothness is supplied. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G]

attribute [local instance] lieGroup_smooth_min_three

 theorem lieCoordinateParametricFlow_contDiffAt_smooth {a b : ℝ}
    (hab : a ≤ b) (t₀ : Icc a b) :
    ContDiffAt ℝ ∞ (lieCoordinateParametricFlow (I := I) (G := G) hab t₀) (0 : E) := by
  have h := curvePicardImplicit_contDiffAt_smooth hab t₀
    (lieFrozenCoordinateField_hasStrictFDerivAt (I := I) (G := G))
    (lieFrozenCoordinateLinearization_square_zero (E := E))
    (lieFrozenCoordinateField_contDiffAt_smooth (I := I) (G := G))
  exact h.comp (0 : E) (contDiffAt_id.prodMk contDiffAt_const)

 theorem lieIdentityCoordinateFlow_state_endpoint_contDiffAt_smooth (t : Icc (-2 : ℝ) 2) :
    ContDiffAt ℝ ∞ (fun v : E => (lieIdentityCoordinateFlow (I := I) (G := G) v t).2) (0 : E) := by
  have h := (ContinuousMap.evalCLM ℝ t : C(Icc (-2 : ℝ) 2, E × E) →L[ℝ] E × E).contDiff.contDiffAt.comp
    (0 : E) (lieCoordinateParametricFlow_contDiffAt_smooth (I := I) (G := G)
      (show (-2 : ℝ) ≤ 2 by norm_num) ⟨0, by constructor <;> norm_num⟩)
  exact h.snd

variable [T2Space G]

 theorem nativeLieExponential_chart_contDiffAt_smooth_zero :
    ContDiffAt ℝ ∞ (fun v : E => extChartAt I (1 : G)
      (nativeLieExponential (I := I) (G := G) v)) (0 : E) := by
  let t₁ : Icc (-2 : ℝ) 2 := ⟨1, by constructor <;> norm_num⟩
  apply (lieIdentityCoordinateFlow_state_endpoint_contDiffAt_smooth (I := I) (G := G) t₁).congr_of_eventuallyEq
  filter_upwards [lieIdentityCoordinateFlow_eventually_chart_native (I := I) (G := G)] with v hv
  exact (hv t₁ (by constructor <;> norm_num)).symm

 theorem nativeLieExponential_contMDiffAt_smooth_zero :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (fun v : E => nativeLieExponential (I := I) (G := G) v) (0 : E) := by
  rw [contMDiffAt_iff]
  refine ⟨(nativeLieExponential_continuous (I := I) (G := G)).continuousAt, ?_⟩
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  simp only [mfld_simps]
  rw [hz]
  exact (nativeLieExponential_chart_contDiffAt_smooth_zero (I := I) (G := G)).contDiffWithinAt

 theorem nativeLieExponentialCoordinateInverse_contDiffAt_smooth :
    ContDiffAt ℝ ∞ (nativeLieExponentialCoordinateInverse (E := E) (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  have hs := nativeLieExponential_chart_contDiffAt_smooth_zero (I := I) (G := G)
  have hd : HasFDerivAt (fun v : E => extChartAt I (1 : G)
      (nativeLieExponential (I := I) (G := G) v))
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (0 : E) :=
    (nativeLieExponential_chart_hasStrictFDerivAt_zero (I := I) (G := G)).hasFDerivAt
  have h := hs.to_localInverse hd (by norm_num : (∞ : ℕ∞ω) ≠ 0)
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  rw [hz] at h
  convert! h using 1

 theorem nativeLieLocalLogarithm_contMDiffAt_smooth_one :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (nativeLieLocalLogarithm (E := E) (I := I) (G := G) : G → E)
      (1 : G) := by
  exact (nativeLieExponentialCoordinateInverse_contDiffAt_smooth (I := I) (G := G)).contMDiffAt.comp
    (1 : G) contMDiffAt_extChartAt

end Hindman168
