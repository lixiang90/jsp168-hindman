import Hindman168.NativeCentralSubspaceQuotientTangent
import Hindman168.NativeCentralSubspaceQuotientCharted
import Hindman168.LieExponentialHomomorphism

/-! Compare the genuine original group exponential with the genuine
native exponential of the actual smooth center quotient. The previously
proved actual smooth-homomorphism ODE uniqueness theorem applies, and
the actual identity differential is the actual model projection. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

variable (V : Submodule ℝ E) [IsClosed (V : Set E)]
  (hV : V ≤ nativeLieCenterModel (I := I) (G := G))

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

theorem nativeCentralSubspaceQuotient_nativeExponential_projection (v : E) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    let F := E ⧸ V
    let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
    QuotientGroup.mk (nativeLieExponential (I := I) (G := G) v) =
      nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q)
        (finiteRealQuotientProjection V v) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' ((nativeCentralSubspaceSubgroup (I := I) V hV))
  let P : E →L[ℝ] F := mfderiv I J q 1
  let π : E →L[ℝ] F := finiteRealQuotientProjection V
  let exp : F → Q := fun x => nativeLieExponential (I := J) (G := Q) x
  have hq : MDifferentiable I J q :=
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV).mdifferentiable (by norm_num)
  let v' : GroupLieAlgebra I G := v
  have h := nativeLieExponential_map (I := I) (J := J) q hq v'
  change q (nativeLieExponential (I := I) (G := G) v) = exp (P v) at h
  have hP : P = π := nativeCentralSubspaceQuotient_mfderiv_eq_projection (I := I) V hV
  exact h.trans (congrArg exp (congrArg (fun A : E →L[ℝ] F => A v) hP))

theorem nativeCentralSubspaceQuotient_coordinateExponential_eq_native (x : E ⧸ V) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV x =
      nativeLieExponential (I := 𝓘(ℝ, E ⧸ V))
        (G := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) x := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let e : F → Q := nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV
  let exp : F → Q := fun x => nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) x
  let v : E := finiteRealQuotientSection V x
  have hv := finiteRealQuotientSection_right V x
  change e x = exp x
  exact (congrArg e hv.symm).trans
    ((nativeCentralSubspaceQuotientExponentialHomeomorph_mk (I := I) V hV v).trans
      ((nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV v).trans
        (congrArg exp hv)))

end Hindman168
