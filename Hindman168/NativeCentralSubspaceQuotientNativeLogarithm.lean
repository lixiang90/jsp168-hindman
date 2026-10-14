import Hindman168.NativeCentralSubspaceQuotientNativeExponential

/-! Compare the true original logarithm with the true native logarithm
of the actual original specified central-subspace quotient. The original quotient is proved
simply connected and nilpotent; its native logarithm is constructed by
the same genuine global inverse theorem, not supplied as a premise. -/

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

theorem nativeCentralSubspaceQuotient_nativeLogarithm_projection (g : G) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    let F := E ⧸ V
    let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
    nativeLieGlobalLogarithm (E := F) (I := 𝓘(ℝ, F)) (G := Q) (QuotientGroup.mk g) =
      finiteRealQuotientProjection V
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let expQ : F → Q := fun x => nativeLieExponential (I := J) (G := Q) x
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let logQ : Q → F := nativeLieGlobalLogarithm (E := F) (I := J) (G := Q)
  let q : G → Q := QuotientGroup.mk
  let π : E →L[ℝ] F := finiteRealQuotientProjection V
  have h : q (exp (log g)) = expQ (π (log g)) :=
    nativeCentralSubspaceQuotient_nativeExponential_projection (I := I) V hV (log g)
  have hg : exp (log g) = g := nativeLieExponential_globalLogarithm (I := I) (G := G) g
  have he : q g = expQ (π (log g)) := (congrArg q hg).symm.trans h
  exact (congrArg logQ he).trans
    (nativeLieGlobalLogarithm_exponential (I := J) (G := Q) (π (log g)))

theorem nativeCentralSubspaceQuotient_coordinateLogarithm_eq_native (x : G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
    letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
    letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
    (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV).symm x =
      nativeLieGlobalLogarithm (E := E ⧸ V)
        (I := 𝓘(ℝ, E ⧸ V)) (G := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) x := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_t2Space (I := I) V hV
  letI := nativeCentralSubspaceQuotient_lieGroup (I := I) V hV
  letI := nativeCentralSubspaceQuotient_simplyConnected (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let logQ : Q → F := nativeLieGlobalLogarithm (E := F) (I := J) (G := Q)
  let e := nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV
  have he := nativeCentralSubspaceQuotient_coordinateExponential_eq_native (I := I) V hV (e.symm x)
  have h := (congrArg logQ he).trans
    (nativeLieGlobalLogarithm_exponential (I := J) (G := Q) (e.symm x))
  change e.symm x = logQ x
  exact h.symm.trans (congrArg logQ (e.apply_symm_apply x))

end Hindman168
