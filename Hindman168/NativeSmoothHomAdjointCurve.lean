import Hindman168.NativeSmoothHomAdjoint
import Hindman168.NativeLieAdjointGenerator

/-! Differentiate the genuine target adjoint along the image of the
original one-parameter curve. The actual smooth homomorphism differential
is used directly; no target exponential comparison is assumed. -/

namespace Hindman168
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

omit [CompleteSpace F] [BoundarylessManifold J K] [T2Space K] in
theorem nativeSmoothHom_adjointCurve_hasDerivAt (q : G →* K)
    (hq : ContMDiff I J ∞ q) (v : E) :
    let P : E →L[ℝ] F := mfderiv I J q 1
    HasDerivAt (fun t : ℝ => nativeLieAdjoint (I := J)
      (q (lieOneParameterCurve (I := I) (G := G) v t)))
      (nativeLieAdjointDifferential (I := J) (G := K) (P v)) 0 := by
  let P : E →L[ℝ] F := mfderiv I J q 1
  let c : ℝ → G := lieOneParameterCurve (I := I) (G := G) v
  have hq0 := (hq.contMDiffAt (x := c 0)).mdifferentiableAt (by norm_num) |>.hasMFDerivAt
  have hc := lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) v
  have hqc := hq0.comp 0 hc
  have ha := ((nativeLieAdjoint_contMDiff (I := J) (G := K)).contMDiffAt
    (x := q (c 0))).mdifferentiableAt (by norm_num) |>.hasMFDerivAt
  have hd := ha.comp 0 hqc
  have hc0 : c (0 : ℝ) = (1 : G) := lieOneParameterCurve_zero (I := I) (G := G) v
  have hf0 : HasFDerivAt (fun t : ℝ => nativeLieAdjoint (I := J) (q (c t)))
      ((mfderiv J 𝓘(ℝ, F →L[ℝ] F) (nativeLieAdjoint (I := J)) (q (c 0)) :
        F →L[ℝ] (F →L[ℝ] F)).comp
        ((mfderiv I J q (c 0) : E →L[ℝ] F).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight v))) 0 := by
    convert! hd.hasFDerivAt using 1
  rw [hc0, q.map_one] at hf0
  have hf : HasFDerivAt (fun t : ℝ => nativeLieAdjoint (I := J) (q (c t)))
      ((nativeLieAdjointDifferential (I := J) (G := K)).comp
        (P.comp ((1 : ℝ →L[ℝ] ℝ).smulRight v))) 0 := hf0
  convert! hf.hasDerivAt using 1
  change nativeLieAdjointDifferential (I := J) (G := K) (P v) =
    nativeLieAdjointDifferential (I := J) (G := K) (P ((1 : ℝ) • v))
  rw [one_smul]

end Hindman168
