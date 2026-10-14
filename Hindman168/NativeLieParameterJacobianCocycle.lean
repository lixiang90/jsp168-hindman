import Hindman168.NativeLieParameterJacobianInitial

/-! The cocycle and time differential equation for the actual relative
parameter derivative. Both follow by differentiating the genuine relative
curve identity; no variation equation is an input. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieIdentityProductParameter_hasMFDerivAt
    {c d : E → G} {C D : E →L[ℝ] E} (hc0 : c 0 = 1) (hd0 : d 0 = 1)
    (hc : HasMFDerivAt 𝓘(ℝ, E) I c 0 C)
    (hd : HasMFDerivAt 𝓘(ℝ, E) I d 0 D) :
    HasMFDerivAt 𝓘(ℝ, E) I (fun w => c w * d w) 0 (C + D) := by
  have hm := ((contMDiff_mul I ∞).mdifferentiableAt (x := (c 0, d 0))
    (by norm_num)).hasMFDerivAt.comp (0 : E) (hc.prodMk hd)
  erw [hc0, hd0] at hm
  apply hm.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let b : E := a
  change mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) (1, 1)
    (C b, D b) = C b + D b
  exact nativeLieMultiplication_mfderiv_identity (I := I) (G := G) (C b) (D b)

 theorem nativeLieCurveParameterJacobian_add (v : E) (t s : ℝ) :
    nativeLieCurveParameterJacobian (I := I) (G := G) v (t + s) =
      nativeLieAdjointCurve (I := I) (G := G) v (-t) *
        nativeLieCurveParameterJacobian (I := I) (G := G) v s +
          nativeLieCurveParameterJacobian (I := I) (G := G) v t := by
  let g : G := lieOneParameterCurve (I := I) (G := G) v (-t)
  let K := nativeLieCurveParameterJacobian (I := I) (G := G) v
  have hconj := (nativeLieConjugation_contMDiff (I := I) g).mdifferentiableAt
    (x := nativeLieRelativeCurve (I := I) (G := G) v (s, 0)) (by norm_num)
  have h := hconj.hasMFDerivAt.comp (0 : E)
    (nativeLieRelativeCurve_state_hasMFDerivAt (I := I) (G := G) v s)
  erw [nativeLieRelativeCurve_state_zero] at h
  have hc : HasMFDerivAt 𝓘(ℝ, E) I
      (fun w : E => g * nativeLieRelativeCurve (I := I) (G := G) v (s, w) * g⁻¹) 0
        ((nativeLieAdjoint (I := I) g).comp (K s)) := by
    convert! h using 1
  have hc0 : g * nativeLieRelativeCurve (I := I) (G := G) v (s, 0) * g⁻¹ = 1 := by
    rw [nativeLieRelativeCurve_state_zero, mul_one, mul_inv_cancel]
  have hp := nativeLieIdentityProductParameter_hasMFDerivAt hc0
    (nativeLieRelativeCurve_state_zero v t) hc
    (nativeLieRelativeCurve_state_hasMFDerivAt (I := I) (G := G) v t)
  have hi : g⁻¹ = lieOneParameterCurve (I := I) (G := G) v t := by
    dsimp [g]
    rw [lieOneParameterCurve_neg_eq_inv, inv_inv]
  have he : (fun w : E =>
      (g * nativeLieRelativeCurve (I := I) (G := G) v (s, w) * g⁻¹) *
        nativeLieRelativeCurve (I := I) (G := G) v (t, w)) =
      (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (t + s, w)) := by
    funext w
    rw [hi]
    exact (nativeLieRelativeCurve_time_add v w t s).symm
  change HasMFDerivAt 𝓘(ℝ, E) I
    (fun w : E => (g * nativeLieRelativeCurve (I := I) (G := G) v (s, w) * g⁻¹) *
      nativeLieRelativeCurve (I := I) (G := G) v (t, w)) 0
        ((nativeLieAdjoint (I := I) g).comp (K s) + K t) at hp
  rw [he] at hp
  convert! hp.mfderiv using 1

 theorem nativeLieCurveParameterJacobian_hasDerivAt (v : E) (t : ℝ) :
    HasDerivAt (nativeLieCurveParameterJacobian (I := I) (G := G) v)
      (nativeLieAdjointCurve (I := I) (G := G) v (-t)) t := by
  let K := nativeLieCurveParameterJacobian (I := I) (G := G) v
  let A := nativeLieAdjointCurve (I := I) (G := G) v (-t)
  have hs : HasDerivAt (fun u : ℝ => u - t) 1 t := (hasDerivAt_id t).sub_const t
  have h0 : HasDerivAt K (1 : E →L[ℝ] E) ((fun u : ℝ => u - t) t) := by
    simp only [sub_self]
    convert! nativeLieCurveParameterJacobian_hasDerivAt_zero (I := I) (G := G) v using 1
  have hd : HasDerivAt (fun u : ℝ => K (u - t)) (1 : E →L[ℝ] E) t := by
    have h := h0.scomp (h := fun u : ℝ => u - t) t hs
    simp only [one_smul] at h
    convert! h using 1
  have hp := (hd.const_mul A).add_const (K t)
  have he : (fun u : ℝ => A * K (u - t) + K t) = K := by
    funext u
    rw [← nativeLieCurveParameterJacobian_add]
    congr 1
    abel
  rw [he] at hp
  simpa only [mul_one] using hp

end Hindman168
