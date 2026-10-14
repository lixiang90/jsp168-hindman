import Hindman168.NativeCentralSubspaceQuotientCharted

/-! Smoothness of the actual original specified central-subspace projection follows from
its proved formula: true global logarithm, actual continuous linear
model quotient, and the constructed actual quotient diffeomorphism. -/

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

theorem nativeCentralSubspaceQuotient_projection_contMDiff :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    ContMDiff I 𝓘(ℝ, E ⧸ V) ∞
      (QuotientGroup.mk : G → G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let π : E →L[ℝ] F := finiteRealQuotientProjection V
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let e : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F Q ∞ :=
    nativeCentralSubspaceQuotientExponentialDiffeomorph (I := I) V hV
  have hπ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ π := π.contDiff.contMDiff
  have h : ContMDiff I 𝓘(ℝ, F) ∞ (fun g : G => e (π (log g))) :=
    e.contMDiff_toFun.comp (hπ.comp (nativeLieGlobalLogarithm_contMDiff (E := E) (I := I)))
  have he : (fun g : G => e (π (log g))) = (QuotientGroup.mk : G → Q) := by
    funext g
    exact (nativeCentralSubspaceQuotientExponentialHomeomorph_mk (I := I) V hV (log g)).trans
      (congrArg (QuotientGroup.mk : G → Q) (nativeLieExponential_globalLogarithm (E := E) (I := I) g))
  rw [he] at h
  exact h

end Hindman168
