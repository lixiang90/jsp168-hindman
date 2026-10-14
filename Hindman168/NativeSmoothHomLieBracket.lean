import Hindman168.NativeSmoothHomAdjointCurve
import Hindman168.NativeLieAdjointInfinitesimal

/-! The actual identity differential of a genuine smooth original group
homomorphism preserves the genuine original Lie brackets. Differentiate
its proved actual adjoint intertwining along original one-parameter
curves, then use the proved identification of adjoint generator with the
actual native vector-field Lie bracket in both original groups. -/

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeSmoothHom_generator_intertwine (q : G →* K)
    (hq : ContMDiff I J ∞ q) (v w : E) :
    let P : E →L[ℝ] F := mfderiv I J q 1
    P (nativeLieAdjointGenerator (I := I) (G := G) v w) =
      nativeLieAdjointGenerator (I := J) (G := K) (P v) (P w) := by
  let P : E →L[ℝ] F := mfderiv I J q 1
  let c : ℝ → G := lieOneParameterCurve (I := I) (G := G) v
  have hL0 : HasDerivAt (fun t : ℝ => nativeLieAdjoint (I := I) (c t) w)
      (nativeLieAdjointDifferential (I := I) (G := G) v w) 0 := by
    simpa only [nativeLieAdjointCurve, map_zero, add_zero] using
      (nativeLieAdjointCurve_hasDerivAt_differential (I := I) (G := G) v).clm_apply
        (hasDerivAt_const (0 : ℝ) w)
  have hL := P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hL0
  have hR : HasDerivAt (fun t : ℝ => nativeLieAdjoint (I := J) (q (c t)) (P w))
      (nativeLieAdjointDifferential (I := J) (G := K) (P v) (P w)) 0 := by
    simpa only [map_zero, add_zero] using
      (nativeSmoothHom_adjointCurve_hasDerivAt (I := I) (J := J) q hq v).clm_apply
        (hasDerivAt_const (0 : ℝ) (P w))
  have he : (fun t : ℝ => P (nativeLieAdjoint (I := I) (c t) w)) =
      (fun t : ℝ => nativeLieAdjoint (I := J) (q (c t)) (P w)) := by
    funext t
    exact congrArg (fun f : E →L[ℝ] F => f w)
      (nativeSmoothHom_adjoint_intertwine (I := I) (J := J) q hq (c t))
  change HasDerivAt (fun t : ℝ => P (nativeLieAdjoint (I := I) (c t) w))
    (P (nativeLieAdjointDifferential (I := I) (G := G) v w)) 0 at hL
  rw [he] at hL
  simpa only [nativeLieAdjointGenerator_eq_differential] using hL.unique hR

theorem nativeSmoothHom_bracket (q : G →* K) (hq : ContMDiff I J ∞ q)
    (v w : GroupLieAlgebra I G) :
    let P : E →L[ℝ] F := mfderiv I J q 1
    let v' : GroupLieAlgebra J K := P v
    let w' : GroupLieAlgebra J K := P w
    P (⁅v, w⁆ : GroupLieAlgebra I G) = (⁅v', w'⁆ : GroupLieAlgebra J K) := by
  let P : E →L[ℝ] F := mfderiv I J q 1
  let v' : GroupLieAlgebra J K := P v
  let w' : GroupLieAlgebra J K := P w
  have h := nativeSmoothHom_generator_intertwine (I := I) (J := J) q hq (show E from v) (show E from w)
  exact (congrArg P (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) v w).symm).trans
    (h.trans (nativeLieAdjointGenerator_eq_native_bracket (I := J) (G := K) v' w'))

end Hindman168
