import Hindman168.NativeCenterQuotientCharted

/-! Smoothness of the actual original center projection follows from
its proved formula: true global logarithm, actual continuous linear
model quotient, and the constructed actual quotient diffeomorphism. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_projection_contMDiff :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    ContMDiff I 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G)) ∞
      (QuotientGroup.mk : G → G ⧸ Subgroup.center G) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let e : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F Q ∞ :=
    nativeCenterQuotientExponentialDiffeomorph (I := I) (G := G)
  have hπ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ π := π.contDiff.contMDiff
  have h : ContMDiff I 𝓘(ℝ, F) ∞ (fun g : G => e (π (log g))) :=
    e.contMDiff_toFun.comp (hπ.comp (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I)))
  have he : (fun g : G => e (π (log g))) = (QuotientGroup.mk : G → Q) := by
    funext g
    exact (nativeCenterQuotientExponentialHomeomorph_mk (I := I) (G := G) (log g)).trans
      (congrArg (QuotientGroup.mk : G → Q) (nativeLieExponential_globalLogarithm (E := E) (I := I) g))
  rw [he] at h
  exact h

end Hindman168
