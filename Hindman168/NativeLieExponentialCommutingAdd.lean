import Hindman168.NativeLieExponentialFiberGenerators

/-! The actual original exponential respects addition of commuting
infinitesimal directions. Its actual adjoint ODE proves fixed vectors;
original conjugation proves commuting curves, whose real product has the
true sum initial velocity. Genuine original integral-curve uniqueness
then proves the addition law without BCH or an exponential logarithm. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointCurve_apply_eq_of_generator_apply_eq_zero {v w : E}
    (h : nativeLieAdjointGenerator (I := I) (G := G) v w = 0) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v t w = w := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u => nativeLieAdjointCurve (I := I) (G := G) v u w) 0 s := by
    intro s
    have hs := (nativeLieAdjointCurve_hasDerivAt (I := I) (G := G) v s).clm_apply
      (hasDerivAt_const s w)
    convert! hs using 1
    change (0 : E) = nativeLieAdjointCurve (I := I) (G := G) v s
      (nativeLieAdjointGenerator (I := I) (G := G) v w) +
        nativeLieAdjointCurve (I := I) (G := G) v s 0
    simp only [h, map_zero, add_zero]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have h0 : nativeLieAdjointCurve (I := I) (G := G) v 0 w = w := by
    rw [nativeLieAdjointCurve_zero]
    rfl
  exact hc.trans h0

 theorem nativeLieCurves_commute_of_generator_apply_eq_zero {v w : E}
    (h : nativeLieAdjointGenerator (I := I) (G := G) v w = 0) (t s : ℝ) :
    Commute (lieOneParameterCurve (I := I) (G := G) v t)
      (lieOneParameterCurve (I := I) (G := G) w s) := by
  have ha : nativeLieAdjoint (I := I) (lieOneParameterCurve (I := I) (G := G) v t) w = w :=
    nativeLieAdjointCurve_apply_eq_of_generator_apply_eq_zero h t
  have hc := nativeLieAdjoint_curve_conjugation (I := I)
    (lieOneParameterCurve (I := I) (G := G) v t) w s
  rw [ha] at hc
  have he := congrArg (fun x : G => x * lieOneParameterCurve (I := I) (G := G) v t) hc
  change lieOneParameterCurve (I := I) (G := G) v t *
    lieOneParameterCurve (I := I) (G := G) w s =
      lieOneParameterCurve (I := I) (G := G) w s * lieOneParameterCurve (I := I) (G := G) v t
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using he

 theorem nativeLieOneParameterCurve_add_of_generator_apply_eq_zero {v w : E}
    (h : nativeLieAdjointGenerator (I := I) (G := G) v w = 0) (t : ℝ) :
    lieOneParameterCurve (I := I) (G := G) (v + w) t =
      lieOneParameterCurve (I := I) (G := G) v t * lieOneParameterCurve (I := I) (G := G) w t := by
  let c : ℝ → G := fun s => lieOneParameterCurve (I := I) (G := G) v s *
    lieOneParameterCurve (I := I) (G := G) w s
  have h0 : c 0 = 1 := by simp only [c, lieOneParameterCurve_zero, mul_one]
  have hadd : ∀ r s : ℝ, c (r + s) = c r * c s := by
    intro r s
    simp only [c, lieOneParameterCurve_add]
    have hc := (nativeLieCurves_commute_of_generator_apply_eq_zero h s r).eq
    calc
      _ = lieOneParameterCurve (I := I) (G := G) v r *
        ((lieOneParameterCurve (I := I) (G := G) v s *
          lieOneParameterCurve (I := I) (G := G) w r) *
            lieOneParameterCurve (I := I) (G := G) w s) := by simp only [mul_assoc]
      _ = _ := by rw [hc]; simp only [mul_assoc]
  have hd := nativeLieIdentityProductCurve_hasMFDerivAt (I := I)
    (lieOneParameterCurve_zero (I := I) (G := G) v)
    (lieOneParameterCurve_zero (I := I) (G := G) w)
    (lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) v)
    (lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) w)
  have hv : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (v + w)) := by
    exact hd
  exact (congrFun (lie_oneParameter_eq_curve_from_zero (I := I) (G := G) (v + w) h0 hadd hv) t).symm

 theorem nativeLieExponential_add_of_generator_apply_eq_zero {v w : E}
    (h : nativeLieAdjointGenerator (I := I) (G := G) v w = 0) :
    nativeLieExponential (I := I) (G := G) (v + w) =
      nativeLieExponential (I := I) (G := G) v * nativeLieExponential (I := I) (G := G) w :=
  nativeLieOneParameterCurve_add_of_generator_apply_eq_zero h 1

 theorem nativeLieExponential_add_of_bracket_eq_zero {v w : GroupLieAlgebra I G}
    (h : ⁅v, w⁆ = 0) : nativeLieExponential (I := I) (G := G) (v + w) =
      nativeLieExponential (I := I) (G := G) v * nativeLieExponential (I := I) (G := G) w := by
  apply nativeLieExponential_add_of_generator_apply_eq_zero
  rwa [nativeLieAdjointGenerator_eq_native_bracket]

end Hindman168
