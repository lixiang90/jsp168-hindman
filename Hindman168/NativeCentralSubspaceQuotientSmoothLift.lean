import Hindman168.NativeCentralSubspaceQuotientSmoothProjection

/-! A genuine global lift of the original specified central-subspace quotient is constructed
using the actual quotient coordinate inverse, the constructed continuous
linear section, and the true original exponential. It is an actual right
inverse of the original group projection and is smooth. -/

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

noncomputable def nativeCentralSubspaceQuotientLift (x : G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) : G :=
  nativeLieExponential (I := I) (G := G)
    (finiteRealQuotientSection V
      ((nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV).symm x))

theorem nativeCentralSubspaceQuotientLift_right (x : G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) :
    QuotientGroup.mk (nativeCentralSubspaceQuotientLift (I := I) V hV x) = x := by
  let F := E ⧸ V
  let e : F ≃ₜ (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) := nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV
  let σ : F →L[ℝ] E := finiteRealQuotientSection V
  have hs : (Submodule.Quotient.mk (σ (e.symm x)) : F) = e.symm x :=
    finiteRealQuotientSection_right V (e.symm x)
  exact (nativeCentralSubspaceQuotientExponentialHomeomorph_mk (I := I) V hV (σ (e.symm x))).symm.trans
    ((congrArg e hs).trans (e.apply_symm_apply x))

theorem nativeCentralSubspaceQuotientLift_contMDiff :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    ContMDiff 𝓘(ℝ, E ⧸ V) I ∞
      (nativeCentralSubspaceQuotientLift (I := I) V hV : (G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) → G) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  let e := nativeCentralSubspaceQuotientExponentialDiffeomorph (I := I) V hV
  let σ : F →L[ℝ] E := finiteRealQuotientSection V
  have hσ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ σ := σ.contDiff.contMDiff
  exact (nativeLieExponential_contMDiff (I := I) (G := G)).comp
    (hσ.comp e.contMDiff_invFun)

end Hindman168
