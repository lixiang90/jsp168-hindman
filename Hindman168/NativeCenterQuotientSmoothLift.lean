import Hindman168.NativeCenterQuotientSmoothProjection

/-! A genuine global lift of the original center quotient is constructed
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

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCenterQuotientLift (x : G ⧸ Subgroup.center G) : G :=
  nativeLieExponential (I := I) (G := G)
    (nativeCenterQuotientSection (I := I) (G := G)
      ((nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)).symm x))

theorem nativeCenterQuotientLift_right (x : G ⧸ Subgroup.center G) :
    QuotientGroup.mk (nativeCenterQuotientLift (I := I) (G := G) x) = x := by
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let e : F ≃ₜ (G ⧸ Subgroup.center G) := nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)
  let σ : F →L[ℝ] E := nativeCenterQuotientSection (I := I) (G := G)
  have hs : (Submodule.Quotient.mk (σ (e.symm x)) : F) = e.symm x :=
    nativeCenterQuotientSection_right (I := I) (G := G) (e.symm x)
  exact (nativeCenterQuotientExponentialHomeomorph_mk (I := I) (G := G) (σ (e.symm x))).symm.trans
    ((congrArg e hs).trans (e.apply_symm_apply x))

theorem nativeCenterQuotientLift_contMDiff :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    ContMDiff 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)) I ∞
      (nativeCenterQuotientLift (I := I) (G := G) : (G ⧸ Subgroup.center G) → G) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let e := nativeCenterQuotientExponentialDiffeomorph (I := I) (G := G)
  let σ : F →L[ℝ] E := nativeCenterQuotientSection (I := I) (G := G)
  have hσ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ σ := σ.contDiff.contMDiff
  exact (nativeLieExponential_contMDiff (I := I) (G := G)).comp
    (hσ.comp e.contMDiff_invFun)

end Hindman168
