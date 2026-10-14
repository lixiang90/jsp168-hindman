import Hindman168.NativeCenterQuotientNativeExponential

/-! Compare the true original logarithm with the true native logarithm
of the actual original center quotient. The original quotient is proved
simply connected and nilpotent; its native logarithm is constructed by
the same genuine global inverse theorem, not supplied as a premise. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_nativeLogarithm_projection (g : G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    let Q := G ⧸ Subgroup.center G
    nativeLieGlobalLogarithm (E := F) (I := 𝓘(ℝ, F)) (G := Q) (QuotientGroup.mk g) =
      nativeCenterQuotientProjection (I := I) (G := G)
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let expQ : F → Q := fun x => nativeLieExponential (I := J) (G := Q) x
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let logQ : Q → F := nativeLieGlobalLogarithm (E := F) (I := J) (G := Q)
  let q : G → Q := QuotientGroup.mk
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  have h : q (exp (log g)) = expQ (π (log g)) :=
    nativeCenterQuotient_nativeExponential_projection (I := I) (G := G) (log g)
  have hg : exp (log g) = g := nativeLieExponential_globalLogarithm (I := I) (G := G) g
  have he : q g = expQ (π (log g)) := (congrArg q hg).symm.trans h
  exact (congrArg logQ he).trans
    (nativeLieGlobalLogarithm_exponential (I := J) (G := Q) (π (log g)))

theorem nativeCenterQuotient_coordinateLogarithm_eq_native (x : G ⧸ Subgroup.center G) :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)).symm x =
      nativeLieGlobalLogarithm (E := E ⧸ nativeLieCenterModel (I := I) (G := G))
        (I := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))) (G := G ⧸ Subgroup.center G) x := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let logQ : Q → F := nativeLieGlobalLogarithm (E := F) (I := J) (G := Q)
  let e := nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)
  have he := nativeCenterQuotient_coordinateExponential_eq_native (I := I) (G := G) (e.symm x)
  have h := (congrArg logQ he).trans
    (nativeLieGlobalLogarithm_exponential (I := J) (G := Q) (e.symm x))
  change e.symm x = logQ x
  exact h.symm.trans (congrArg logQ (e.apply_symm_apply x))

end Hindman168
