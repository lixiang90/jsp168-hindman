import Hindman168.LieOneParameterExponential

/-! The initial native derivative determines a genuine one-parameter
subgroup. The group law transports the zero-time derivative to every
time, proving the actual invariant-field differential equation; global
ODE uniqueness then identifies it with the constructed exponential. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G] [T2Space G]

 omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G]
   [LieGroup I (minSmoothness ℝ 3) G] in
 theorem lie_invariant_field_one (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v (1 : G) = v := by
  unfold mulInvariantVectorField
  have heq : (fun x : G => 1 * x) = id := funext one_mul
  rw [heq, mfderiv_id]
  rfl

 omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem lie_oneParameter_hasMFDerivAt_from_zero
    (v : E) {c : ℝ → G} (h0 : c 0 = 1)
    (hadd : ∀ r s : ℝ, c (r + s) = c r * c s)
    (hv : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ) I c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := I) (G := G) v (c t) : E)) := by
  have hs : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun u : ℝ => u - t) t
      (ContinuousLinearMap.id ℝ ℝ) := ((hasFDerivAt_id t).sub_const t).hasMFDerivAt
  have hv' : HasMFDerivAt 𝓘(ℝ) I c ((fun u : ℝ => u - t) t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)  := by
    convert hv using 1 <;> first | rfl | simp only [sub_self]
  have hc := hv'.comp (f := fun u : ℝ => u - t) t hs
  have hn : minSmoothness ℝ 3 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness).ne'
  have hd : MDifferentiableAt I I (fun x : G => c t * x) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  have hd' : HasMFDerivAt I I (fun x : G => c t * x)
      ((c ∘ (fun u : ℝ => u - t)) t)
      (mfderiv I I (fun x : G => c t * x) (1 : G)) := by
    convert hd.hasMFDerivAt using 1
    first | rfl | simp only [Function.comp_apply, sub_self, h0]
  have h := hd'.comp t hc
  have heq : (fun x : G => c t * x) ∘ (c ∘ (fun u : ℝ => u - t)) = c := by
    funext u
    change c t * c (u - t) = c u
    rw [← hadd t (u - t)]
    congr 1
    abel
  rw [heq] at h
  apply h.congr_mfderiv
  change ((mfderiv I I (fun x : G => c t * x) (1 : G) : E →L[ℝ] E).comp
    (((1 : ℝ →L[ℝ] ℝ).smulRight v).comp (ContinuousLinearMap.id ℝ ℝ))) =
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (mulInvariantVectorField (I := I) (G := G) v (c t) : E)
  rw [ContinuousLinearMap.comp_id]
  apply ContinuousLinearMap.ext
  intro a
  change (mfderiv I I (fun x : G => c t * x) (1 : G) : E →L[ℝ] E) (a • v) =
    a • ((mfderiv I I (fun x : G => c t * x) (1 : G) : E →L[ℝ] E) v)
  exact (mfderiv I I (fun x : G => c t * x) (1 : G) : E →L[ℝ] E).map_smul a v

 omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem lie_oneParameter_integral_from_zero
    (v : E) {c : ℝ → G} (h0 : c 0 = 1)
    (hadd : ∀ r s : ℝ, c (r + s) = c r * c s)
    (hv : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    IsMIntegralCurve c (mulInvariantVectorField (I := I) (G := G) v) :=
  fun t => lie_oneParameter_hasMFDerivAt_from_zero v h0 hadd hv t

 theorem lie_oneParameter_eq_curve_from_zero
    (v : E) {c : ℝ → G} (h0 : c 0 = 1)
    (hadd : ∀ r s : ℝ, c (r + s) = c r * c s)
    (hv : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    c = lieOneParameterCurve (I := I) (G := G) v :=
  lieOneParameterCurve_unique v (lie_oneParameter_integral_from_zero v h0 hadd hv) h0

 theorem nativeLieExponential_eq_oneParameter_from_zero
    (v : E) {c : ℝ → G} (h0 : c 0 = 1)
    (hadd : ∀ r s : ℝ, c (r + s) = c r * c s)
    (hv : HasMFDerivAt 𝓘(ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    nativeLieExponential (I := I) (G := G) v = c 1 :=
  (congrFun (lie_oneParameter_eq_curve_from_zero v h0 hadd hv) 1).symm

 theorem lieOneParameterCurve_hasMFDerivAt_zero (v : GroupLieAlgebra I G) :
    HasMFDerivAt 𝓘(ℝ) I (lieOneParameterCurve v) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v : E)) := by
  have h := lieOneParameterCurve_integral v 0
  erw [lieOneParameterCurve_zero, lie_invariant_field_one] at h
  exact h

 theorem nativeLieExponential_ray_hasMFDerivAt_zero (v : GroupLieAlgebra I G) :
    HasMFDerivAt 𝓘(ℝ) I (fun t : ℝ => nativeLieExponential (t • v)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v : E)) := by
  have heq : (fun t : ℝ => nativeLieExponential (t • v)) = lieOneParameterCurve v :=
    funext (nativeLieExponential_smul v)
  rw [heq]
  exact lieOneParameterCurve_hasMFDerivAt_zero v

end Hindman168
