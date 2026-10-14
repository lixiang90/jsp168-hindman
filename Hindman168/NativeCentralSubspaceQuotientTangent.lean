import Hindman168.NativeCentralSubspaceQuotientDifferential
import Hindman168.HomeomorphSingletonDifferential

/-! The actual original specified central-subspace projection differential at identity is
exactly the genuine real submodule quotient projection. Differentiate
the actual q composed Exp equals quotient-coordinate Exp composed pi
identity; actual original Exp has identity derivative at zero and the
actual quotient coordinate chart has identity derivative. -/

namespace Hindman168
open Function
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

theorem nativeCentralSubspaceQuotient_mfderiv_eq_projection :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    mfderiv I J (QuotientGroup.mk : G → G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) 1 =
      finiteRealQuotientProjection V := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  letI := nativeCentralSubspaceQuotient_isManifold (I := I) V hV
  let F := E ⧸ V
  let Q := G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let π : E →L[ℝ] F := finiteRealQuotientProjection V
  let e := nativeCentralSubspaceQuotientExponentialDiffeomorph (I := I) V hV
  change mfderiv I J q (1 : G) = π
  have hq : MDifferentiableAt I J q (exp 0) :=
    (nativeCentralSubspaceQuotient_projection_contMDiff (I := I) V hV).mdifferentiableAt (by norm_num)
  have hx : MDifferentiableAt 𝓘(ℝ, E) I exp 0 :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have he : MDifferentiableAt J J e (π 0) := e.contMDiff_toFun.mdifferentiableAt (by norm_num)
  have hπsmooth : ContMDiff 𝓘(ℝ, E) J ∞ π := π.contDiff.contMDiff
  have hp : MDifferentiableAt 𝓘(ℝ, E) J π 0 := hπsmooth.mdifferentiableAt (by norm_num)
  have hfun : q ∘ exp = e ∘ π := funext fun v =>
    (nativeCentralSubspaceQuotientExponentialHomeomorph_mk (I := I) V hV v).symm
  have hleft := mfderiv_comp (0 : E) hq hx
  rw [hfun] at hleft
  have hz : exp (0 : E) = 1 := nativeLieExponential_zero (I := I) (G := G)
  have hd : mfderiv 𝓘(ℝ, E) I exp 0 = ContinuousLinearMap.id ℝ E :=
    nativeLieExponential_mfderiv_zero (I := I) (G := G)
  rw [hz, hd] at hleft
  have hleft' : mfderiv 𝓘(ℝ, E) J (e ∘ π) 0 = mfderiv I J q 1 :=
    hleft.trans (ContinuousLinearMap.comp_id (mfderiv I J q 1 : E →L[ℝ] F))
  have hright := mfderiv_comp (0 : E) he hp
  have hep : mfderiv J J e (π 0) = ContinuousLinearMap.id ℝ F := by
    rw [π.map_zero]
    exact homeomorphSingleton_mfderiv (nativeCentralSubspaceQuotientExponentialHomeomorph (I := I) V hV) 0
  have hπ : mfderiv 𝓘(ℝ, E) J π 0 = π := π.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hep, hπ] at hright
  have hright' : mfderiv 𝓘(ℝ, E) J (e ∘ π) 0 = π :=
    hright.trans (ContinuousLinearMap.id_comp π)
  exact hleft'.symm.trans hright'

theorem nativeCentralSubspaceQuotient_mfderiv_ker :
    letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
    let J := 𝓘(ℝ, E ⧸ V)
    (mfderiv I J (QuotientGroup.mk : G → G ⧸ (nativeCentralSubspaceSubgroup (I := I) V hV)) 1).ker =
      V := by
  letI := nativeCentralSubspaceQuotientChartedSpace (I := I) V hV
  let F := E ⧸ V
  exact (congrArg (fun f : E →L[ℝ] F => f.ker)
    (nativeCentralSubspaceQuotient_mfderiv_eq_projection (I := I) V hV)).trans
      (Submodule.ker_mkQ (V))

end Hindman168
