import Hindman168.NativeCenterQuotientTangent
import Hindman168.NativeCenterQuotientSeparation
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

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_nativeExponential_projection (v : E) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    QuotientGroup.mk (nativeLieExponential (I := I) (G := G) v) =
      nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q)
        (nativeCenterQuotientProjection (I := I) (G := G) v) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let P : E →L[ℝ] F := mfderiv I J q 1
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  let exp : F → Q := fun x => nativeLieExponential (I := J) (G := Q) x
  have hq : MDifferentiable I J q :=
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)).mdifferentiable (by norm_num)
  let v' : GroupLieAlgebra I G := v
  have h := nativeLieExponential_map (I := I) (J := J) q hq v'
  change q (nativeLieExponential (I := I) (G := G) v) = exp (P v) at h
  have hP : P = π := nativeCenterQuotient_mfderiv_eq_projection (I := I) (G := G)
  exact h.trans (congrArg exp (congrArg (fun A : E →L[ℝ] F => A v) hP))

theorem nativeCenterQuotient_coordinateExponential_eq_native (x : E ⧸ nativeLieCenterModel (I := I) (G := G)) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    nativeCenterQuotientExponentialHomeomorph (I := I) (G := G) x =
      nativeLieExponential (I := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)))
        (G := G ⧸ Subgroup.center G) x := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let e : F → Q := nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)
  let exp : F → Q := fun x => nativeLieExponential (I := 𝓘(ℝ, F)) (G := Q) x
  let v : E := nativeCenterQuotientSection (I := I) (G := G) x
  have hv := nativeCenterQuotientSection_right (I := I) (G := G) x
  change e x = exp x
  exact (congrArg e hv.symm).trans
    ((nativeCenterQuotientExponentialHomeomorph_mk (I := I) (G := G) v).trans
      ((nativeCenterQuotient_nativeExponential_projection (I := I) (G := G) v).trans
        (congrArg exp hv)))

end Hindman168
