import Hindman168.LieCoordinateFlowIdentification
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The derivative of the original native exponential at zero. The
actual controlled coordinate flow is first identified with the native
curves; only then is its endpoint derivative transferred to the
original exponential. The inverse-function theorem supplies a genuine
local coordinate inverse. No exponential derivative is assumed. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G] [T2Space G]

 theorem nativeLieExponential_chart_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (fun v : E => extChartAt I (1 : G)
      (nativeLieExponential (I := I) (G := G) v))
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  let t₁ : Icc (-2 : ℝ) 2 := ⟨1, by constructor <;> norm_num⟩
  have h := lieCoordinateParametricFlow_state_endpoint_hasStrictFDerivAt (I := I) (G := G)
    (show (-2 : ℝ) ≤ 2 by norm_num) ⟨0, by constructor <;> norm_num⟩ t₁
  change HasStrictFDerivAt
    (fun v : E => (lieIdentityCoordinateFlow (I := I) (G := G) v t₁).2)
    (((1 : ℝ) - 0) • ContinuousLinearMap.id ℝ E) (0 : E) at h
  simp only [sub_zero, one_smul] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [lieIdentityCoordinateFlow_eventually_chart_native (I := I) (G := G)] with v hv
  exact hv t₁ (by constructor <;> norm_num)

 theorem nativeLieExponential_hasMFDerivAt_zero :
    HasMFDerivAt 𝓘(ℝ, E) I (fun v : E => nativeLieExponential (I := I) (G := G) v) (0 : E)
      (ContinuousLinearMap.id ℝ E) := by
  refine ⟨(nativeLieExponential_continuous (I := I) (G := G)).continuousAt, ?_⟩
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  simp only [writtenInExtChartAt, mfld_simps]
  rw [hz]
  exact (nativeLieExponential_chart_hasStrictFDerivAt_zero (I := I) (G := G)).hasFDerivAt.hasFDerivWithinAt

 theorem nativeLieExponential_mfderiv_zero :
    mfderiv 𝓘(ℝ, E) I (fun v : E => nativeLieExponential (I := I) (G := G) v) (0 : E) =
      ContinuousLinearMap.id ℝ E :=
  (nativeLieExponential_hasMFDerivAt_zero (I := I) (G := G)).mfderiv

 noncomputable def nativeLieExponentialCoordinateInverse : E → E :=
  (show HasStrictFDerivAt (fun v : E => extChartAt I (1 : G)
    (nativeLieExponential (I := I) (G := G) v))
    (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 from
      nativeLieExponential_chart_hasStrictFDerivAt_zero).localInverse _ _ _

 theorem nativeLieExponentialCoordinateInverse_left :
    ∀ᶠ v : E in 𝓝 0, nativeLieExponentialCoordinateInverse (E := E) (I := I) (G := G)
      (extChartAt I (1 : G) (nativeLieExponential (I := I) (G := G) v)) = v :=
  (show HasStrictFDerivAt (fun v : E => extChartAt I (1 : G)
    (nativeLieExponential (I := I) (G := G) v))
    (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 from
      nativeLieExponential_chart_hasStrictFDerivAt_zero).eventually_left_inverse

 theorem nativeLieExponentialCoordinateInverse_right :
    ∀ᶠ z : E in 𝓝 (extChartAt I (1 : G) (1 : G)),
      extChartAt I (1 : G) (nativeLieExponential (I := I) (G := G)
        (nativeLieExponentialCoordinateInverse (E := E) (I := I) (G := G) z)) = z := by
  have h := (show HasStrictFDerivAt (fun v : E => extChartAt I (1 : G)
    (nativeLieExponential (I := I) (G := G) v))
    (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 from
      nativeLieExponential_chart_hasStrictFDerivAt_zero).eventually_right_inverse
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  rw [hz] at h
  convert! h using 1

 theorem nativeLieExponentialCoordinateInverse_hasStrictFDerivAt :
    HasStrictFDerivAt (nativeLieExponentialCoordinateInverse (E := E) (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) (extChartAt I (1 : G) (1 : G)) := by
  have h := (show HasStrictFDerivAt (fun v : E => extChartAt I (1 : G)
    (nativeLieExponential (I := I) (G := G) v))
    (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 from
      nativeLieExponential_chart_hasStrictFDerivAt_zero).to_localInverse
  have hz : nativeLieExponential (I := I) (G := G) (0 : E) = 1 :=
    nativeLieExponential_zero (I := I) (G := G)
  rw [hz] at h
  apply h.congr_fderiv
  ext v
  rfl

end Hindman168
