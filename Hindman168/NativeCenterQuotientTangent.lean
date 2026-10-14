import Hindman168.NativeCenterQuotientDifferential
import Hindman168.HomeomorphSingletonDifferential

/-! The actual original center projection differential at identity is
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

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCenterQuotient_mfderiv_eq_projection :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    mfderiv I J (QuotientGroup.mk : G → G ⧸ Subgroup.center G) 1 =
      nativeCenterQuotientProjection (I := I) (G := G) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_isManifold (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  let Q := G ⧸ Subgroup.center G
  let J := 𝓘(ℝ, F)
  let q : G → Q := QuotientGroup.mk
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let π : E →L[ℝ] F := nativeCenterQuotientProjection (I := I) (G := G)
  let e := nativeCenterQuotientExponentialDiffeomorph (I := I) (G := G)
  change mfderiv I J q (1 : G) = π
  have hq : MDifferentiableAt I J q (exp 0) :=
    (nativeCenterQuotient_projection_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hx : MDifferentiableAt 𝓘(ℝ, E) I exp 0 :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have he : MDifferentiableAt J J e (π 0) := e.contMDiff_toFun.mdifferentiableAt (by norm_num)
  have hπsmooth : ContMDiff 𝓘(ℝ, E) J ∞ π := π.contDiff.contMDiff
  have hp : MDifferentiableAt 𝓘(ℝ, E) J π 0 := hπsmooth.mdifferentiableAt (by norm_num)
  have hfun : q ∘ exp = e ∘ π := funext fun v =>
    (nativeCenterQuotientExponentialHomeomorph_mk (I := I) (G := G) v).symm
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
    exact homeomorphSingleton_mfderiv (nativeCenterQuotientExponentialHomeomorph (I := I) (G := G)) 0
  have hπ : mfderiv 𝓘(ℝ, E) J π 0 = π := π.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hep, hπ] at hright
  have hright' : mfderiv 𝓘(ℝ, E) J (e ∘ π) 0 = π :=
    hright.trans (ContinuousLinearMap.id_comp π)
  exact hleft'.symm.trans hright'

theorem nativeCenterQuotient_mfderiv_ker :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    let J := 𝓘(ℝ, E ⧸ nativeLieCenterModel (I := I) (G := G))
    (mfderiv I J (QuotientGroup.mk : G → G ⧸ Subgroup.center G) 1).ker =
      nativeLieCenterModel (I := I) (G := G) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
  exact (congrArg (fun f : E →L[ℝ] F => f.ker)
    (nativeCenterQuotient_mfderiv_eq_projection (I := I) (G := G))).trans
      (Submodule.ker_mkQ (nativeLieCenterModel (I := I) (G := G)))

end Hindman168
