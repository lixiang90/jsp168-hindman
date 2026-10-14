import Hindman168.NativeLieAdjointCurve
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! The actual native adjoint generator is linear in its original tangent
parameter. The genuine manifold chain rule identifies it with the actual
identity derivative of the original adjoint. Its action is alternating and
equivariant under original conjugation. This still does not identify that
action with the native vector-field Lie bracket. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieAdjointDifferential : E →L[ℝ] (E →L[ℝ] E) :=
  mfderiv I 𝓘(ℝ, E →L[ℝ] E) (nativeLieAdjoint (I := I) : G → E →L[ℝ] E) (1 : G)

 theorem nativeLieAdjointCurve_hasDerivAt_differential (v : E) :
    HasDerivAt (nativeLieAdjointCurve (I := I) (G := G) v)
      (nativeLieAdjointDifferential (I := I) (G := G) v) 0 := by
  have ha := ((nativeLieAdjoint_contMDiff (I := I) (G := G)).contMDiffAt
    (x := lieOneParameterCurve (I := I) (G := G) v 0)).mdifferentiableAt
      (by norm_num) |>.hasMFDerivAt
  have hd := ha.comp 0 (lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) v)
  erw [lieOneParameterCurve_zero] at hd
  have hfd : HasFDerivAt (nativeLieAdjointCurve (I := I) (G := G) v)
      ((nativeLieAdjointDifferential (I := I) (G := G)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight v)) 0 := by
    convert! hd.hasFDerivAt using 1
  convert! hfd.hasDerivAt using 1
  change nativeLieAdjointDifferential (I := I) (G := G) v =
    nativeLieAdjointDifferential (I := I) (G := G) ((1 : ℝ) • v)
  rw [one_smul]

 theorem nativeLieAdjointGenerator_eq_differential (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v =
      nativeLieAdjointDifferential (I := I) (G := G) v :=
  (nativeLieAdjointCurve_hasDerivAt_differential v).deriv

 theorem nativeLieAdjointGenerator_add (v w : E) :
    nativeLieAdjointGenerator (I := I) (G := G) (v + w) =
      nativeLieAdjointGenerator (I := I) (G := G) v + nativeLieAdjointGenerator (I := I) (G := G) w := by
  simp only [nativeLieAdjointGenerator_eq_differential, map_add]

 theorem nativeLieAdjointGenerator_smul (a : ℝ) (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) (a • v) =
      a • nativeLieAdjointGenerator (I := I) (G := G) v := by
  simp only [nativeLieAdjointGenerator_eq_differential, map_smul]

 theorem nativeLieAdjointGenerator_zero :
    nativeLieAdjointGenerator (I := I) (G := G) (0 : E) = 0 := by
  rw [nativeLieAdjointGenerator_eq_differential, map_zero]

 theorem nativeLieAdjointGenerator_self (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v v = 0 := by
  have hd := (nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G) v).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have heq : (fun t : ℝ => nativeLieAdjointCurve (I := I) (G := G) v t v) = fun _ => v := by
    funext t
    exact nativeLieAdjoint_curve_self v t
  rw [heq] at hd
  simpa only [map_zero, add_zero] using hd.unique (hasDerivAt_const (0 : ℝ) v)

 theorem nativeLieAdjointGenerator_alternating (v w : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v w =
      -nativeLieAdjointGenerator (I := I) (G := G) w v := by
  have h := nativeLieAdjointGenerator_self (I := I) (G := G) (v + w)
  rw [nativeLieAdjointGenerator_add, add_apply,
    map_add, map_add, nativeLieAdjointGenerator_self,
    nativeLieAdjointGenerator_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

 theorem nativeLieAdjointGenerator_continuous :
    Continuous (nativeLieAdjointGenerator (I := I) (G := G) : E → E →L[ℝ] E) := by
  have heq : (nativeLieAdjointGenerator (I := I) (G := G) : E → E →L[ℝ] E) =
      nativeLieAdjointDifferential (I := I) (G := G) :=
    funext nativeLieAdjointGenerator_eq_differential
  rw [heq]
  exact (nativeLieAdjointDifferential (I := I) (G := G)).continuous

 theorem nativeLieAdjointCurve_conjugation (g : G) (v : E) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) (nativeLieAdjoint (I := I) g v) t =
      nativeLieAdjoint (I := I) g * nativeLieAdjointCurve (I := I) (G := G) v t *
        nativeLieAdjoint (I := I) g⁻¹ := by
  unfold nativeLieAdjointCurve
  rw [← nativeLieAdjoint_curve_conjugation]
  simp only [nativeLieAdjoint_mul]
  rfl

 theorem nativeLieAdjointGenerator_conjugation (g : G) (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) (nativeLieAdjoint (I := I) g v) =
      nativeLieAdjoint (I := I) g * nativeLieAdjointGenerator (I := I) (G := G) v *
        nativeLieAdjoint (I := I) g⁻¹ := by
  have hd := ((nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G) v).const_mul
    (nativeLieAdjoint (I := I) g)).mul_const (nativeLieAdjoint (I := I) g⁻¹)
  have heq : (fun t : ℝ => nativeLieAdjoint (I := I) g *
      nativeLieAdjointCurve (I := I) (G := G) v t * nativeLieAdjoint (I := I) g⁻¹) =
      nativeLieAdjointCurve (I := I) (G := G) (nativeLieAdjoint (I := I) g v) := by
    funext t
    exact (nativeLieAdjointCurve_conjugation g v t).symm
  rw [heq] at hd
  exact ((nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G)
    (nativeLieAdjoint (I := I) g v)).unique hd)

 theorem nativeLieAdjointGenerator_equivariant (g : G) (v w : E) :
    nativeLieAdjointGenerator (I := I) (G := G) (nativeLieAdjoint (I := I) g v)
        (nativeLieAdjoint (I := I) g w) =
      nativeLieAdjoint (I := I) g (nativeLieAdjointGenerator (I := I) (G := G) v w) := by
  rw [nativeLieAdjointGenerator_conjugation]
  change nativeLieAdjoint (I := I) g (nativeLieAdjointGenerator (I := I) (G := G) v
    (nativeLieAdjoint (I := I) g⁻¹ (nativeLieAdjoint (I := I) g w))) = _
  rw [nativeLieAdjoint_inv_apply]

 theorem nativeLieAdjointGenerator_joint_continuous :
    Continuous (fun p : E × E => nativeLieAdjointGenerator (I := I) (G := G) p.1 p.2) :=
  (nativeLieAdjointGenerator_continuous.comp continuous_fst).clm_apply continuous_snd

 theorem nativeLieAdjointGenerator_hasFDerivAt (v : E) :
    HasFDerivAt (nativeLieAdjointGenerator (I := I) (G := G))
      (nativeLieAdjointDifferential (I := I) (G := G)) v := by
  have heq : (nativeLieAdjointGenerator (I := I) (G := G) : E → E →L[ℝ] E) =
      nativeLieAdjointDifferential (I := I) (G := G) :=
    funext nativeLieAdjointGenerator_eq_differential
  rw [heq]
  exact (nativeLieAdjointDifferential (I := I) (G := G)).hasFDerivAt

 theorem nativeLieAdjointCurve_action_hasDerivAt_zero (v w : E) :
    HasDerivAt (fun t : ℝ => nativeLieAdjointCurve (I := I) (G := G) v t w)
      (nativeLieAdjointGenerator (I := I) (G := G) v w) 0 := by
  have h := (nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G) v).clm_apply
    (hasDerivAt_const (0 : ℝ) w)
  simpa only [map_zero, add_zero] using h

 theorem nativeLieAdjointGenerator_action_leibniz (u v w : E) :
    nativeLieAdjointGenerator (I := I) (G := G) u
        (nativeLieAdjointGenerator (I := I) (G := G) v w) =
      nativeLieAdjointGenerator (I := I) (G := G)
        (nativeLieAdjointGenerator (I := I) (G := G) u v) w +
      nativeLieAdjointGenerator (I := I) (G := G) v
        (nativeLieAdjointGenerator (I := I) (G := G) u w) := by
  let A := nativeLieAdjointCurve (I := I) (G := G) u
  let B := nativeLieAdjointGenerator (I := I) (G := G)
  have hv : HasDerivAt (fun t : ℝ => A t v) (B u v) 0 :=
    nativeLieAdjointCurve_action_hasDerivAt_zero u v
  have hw : HasDerivAt (fun t : ℝ => A t w) (B u w) 0 :=
    nativeLieAdjointCurve_action_hasDerivAt_zero u w
  have hb := (nativeLieAdjointGenerator_hasFDerivAt (I := I) (G := G) (A 0 v)).comp_hasDerivAt 0 hv
  have hl := hb.clm_apply hw
  have hr : HasDerivAt (fun t : ℝ => A t (B v w)) (B u (B v w)) 0 :=
    nativeLieAdjointCurve_action_hasDerivAt_zero u (B v w)
  have heq : (fun t : ℝ => B (A t v) (A t w)) = (fun t : ℝ => A t (B v w)) := by
    funext t
    exact nativeLieAdjointGenerator_equivariant
      (lieOneParameterCurve (I := I) (G := G) u t) v w
  change HasDerivAt (fun t : ℝ => B (A t v) (A t w))
    (nativeLieAdjointDifferential (I := I) (G := G) (B u v) (A 0 w) +
      B (A 0 v) (B u w)) 0 at hl
  rw [heq] at hl
  have h := (hl.unique hr).symm
  simpa only [A, B, nativeLieAdjointCurve_zero, nativeLieAdjointGenerator_eq_differential,
    one_apply_eq_self] using h

 theorem nativeLieAdjointGenerator_commutator (u v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) u * nativeLieAdjointGenerator (I := I) (G := G) v -
        nativeLieAdjointGenerator (I := I) (G := G) v * nativeLieAdjointGenerator (I := I) (G := G) u =
      nativeLieAdjointGenerator (I := I) (G := G)
        (nativeLieAdjointGenerator (I := I) (G := G) u v) := by
  apply ContinuousLinearMap.ext
  intro w
  change nativeLieAdjointGenerator (I := I) (G := G) u
      (nativeLieAdjointGenerator (I := I) (G := G) v w) -
    nativeLieAdjointGenerator (I := I) (G := G) v
      (nativeLieAdjointGenerator (I := I) (G := G) u w) = _
  rw [nativeLieAdjointGenerator_action_leibniz, add_sub_cancel_right]

end Hindman168
