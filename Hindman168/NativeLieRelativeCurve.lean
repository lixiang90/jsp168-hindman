import Hindman168.NativeLieGroupNilpotency

/-! The genuine relative variation gamma-v(-t)*gamma-(v+w)(t) of the
original one-parameter curve. All values and smoothness are derived from
the original curve; no parameter variation or logarithmic derivative is
supplied. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem lieOneParameterCurve_neg_eq_inv (v : E) (t : ℝ) :
    lieOneParameterCurve (I := I) (G := G) v (-t) =
      (lieOneParameterCurve (I := I) (G := G) v t)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← lieOneParameterCurve_add, neg_add_cancel, lieOneParameterCurve_zero]

 theorem lieOneParameterCurve_neg_parameter (v : E) (t : ℝ) :
    lieOneParameterCurve (I := I) (G := G) (-v) t =
      lieOneParameterCurve (I := I) (G := G) v (-t) := by
  have h := congrFun (lieOneParameterCurve_smul (I := I) (G := G) v (-1)) t
  simp only [neg_one_smul, comp_apply, mul_neg_one] at h
  convert! h using 1

noncomputable def nativeLieRelativeCurve (v : E) (p : ℝ × E) : G :=
  lieOneParameterCurve (I := I) (G := G) v (-p.1) *
    lieOneParameterCurve (I := I) (G := G) (v + p.2) p.1

noncomputable def nativeLieRelativeCoordinateCurve (v : E) (p : ℝ × E) : E :=
  extChartAt I (1 : G) (nativeLieRelativeCurve (I := I) (G := G) v p)

 theorem nativeLieRelativeCurve_time_zero (v w : E) :
    nativeLieRelativeCurve (I := I) (G := G) v (0, w) = 1 := by
  simp only [nativeLieRelativeCurve, neg_zero, lieOneParameterCurve_zero, one_mul]

 theorem nativeLieRelativeCurve_state_zero (v : E) (t : ℝ) :
    nativeLieRelativeCurve (I := I) (G := G) v (t, 0) = 1 := by
  simp only [nativeLieRelativeCurve, add_zero, lieOneParameterCurve_neg_eq_inv, inv_mul_cancel]

 theorem nativeLieRelativeCurve_contMDiff (v : E) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (nativeLieRelativeCurve (I := I) (G := G) v) := by
  have hl := (lieOneParameterCurve_joint_contMDiff (I := I) (G := G)).comp
    ((contMDiff_const : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun _ : ℝ × E => v)).prodMk contMDiff_fst.neg)
  have hr := (lieOneParameterCurve_joint_contMDiff (I := I) (G := G)).comp
    (((contMDiff_const : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun _ : ℝ × E => v)).add contMDiff_snd).prodMk contMDiff_fst)
  exact hl.mul hr

 theorem nativeLieRelativeCoordinateCurve_contDiffAt (v : E) (t : ℝ) :
    ContDiffAt ℝ ∞ (nativeLieRelativeCoordinateCurve (I := I) (G := G) v) (t, 0) := by
  have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (1 : G))
      (nativeLieRelativeCurve (I := I) (G := G) v (t, 0)) := by
    rw [nativeLieRelativeCurve_state_zero]
    exact contMDiffAt_extChartAt
  have h := hc.comp (t, (0 : E))
    (nativeLieRelativeCurve_contMDiff (I := I) (G := G) v).contMDiffAt
  rw [← modelWithCornersSelf_prod] at h
  rw [chartedSpaceSelf_prod] at h
  convert! h.contDiffAt using 1

 theorem nativeLieRelativeCurve_time_add (v w : E) (t s : ℝ) :
    nativeLieRelativeCurve (I := I) (G := G) v (t + s, w) =
      lieOneParameterCurve (I := I) (G := G) v (-t) *
        nativeLieRelativeCurve (I := I) (G := G) v (s, w) *
          lieOneParameterCurve (I := I) (G := G) v t *
            nativeLieRelativeCurve (I := I) (G := G) v (t, w) := by
  unfold nativeLieRelativeCurve
  rw [neg_add, lieOneParameterCurve_add]
  have hsum : lieOneParameterCurve (I := I) (G := G) (v + w) (t + s) =
      lieOneParameterCurve (I := I) (G := G) (v + w) s *
        lieOneParameterCurve (I := I) (G := G) (v + w) t := by
    rw [add_comm t s, lieOneParameterCurve_add]
  rw [hsum, lieOneParameterCurve_neg_eq_inv, lieOneParameterCurve_neg_eq_inv]
  group

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieIdentityProductCurve_hasMFDerivAt
    {c d : ℝ → G} {u w : E} (hc0 : c 0 = 1) (hd0 : d 0 = 1)
    (hc : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight u))
    (hd : HasMFDerivAt 𝓘(ℝ) I d 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    HasMFDerivAt 𝓘(ℝ) I (fun t => c t * d t) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (u + w)) := by
  have hm := ((contMDiff_mul I ∞).mdifferentiableAt (x := (c 0, d 0))
    (by norm_num)).hasMFDerivAt.comp 0 (hc.prodMk hd)
  erw [hc0, hd0] at hm
  apply hm.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let b : ℝ := a
  change mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) (1, 1)
    (b • u, b • w) = b • (u + w)
  rw [nativeLieMultiplication_mfderiv_identity, smul_add]

 theorem nativeLieRelativeCurve_hasMFDerivAt_time_zero (v w : E) :
    HasMFDerivAt 𝓘(ℝ) I (fun t => nativeLieRelativeCurve (I := I) (G := G) v (t, w)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
  have he : (fun t : ℝ => lieOneParameterCurve (I := I) (G := G) v (-t)) =
      lieOneParameterCurve (I := I) (G := G) (-v) := by
    funext t
    exact (lieOneParameterCurve_neg_parameter v t).symm
  have hc := lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) (-v)
  rw [← he] at hc
  have h := nativeLieIdentityProductCurve_hasMFDerivAt
    (by simp only [neg_zero, lieOneParameterCurve_zero])
    (lieOneParameterCurve_zero (v + w)) hc
    (lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) (v + w))
  convert! h using 1
  congr 1
  abel

end Hindman168
