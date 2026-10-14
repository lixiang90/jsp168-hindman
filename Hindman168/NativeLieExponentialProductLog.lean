import Hindman168.NativeLieLogarithmPicard

/-! The genuine finite Picard curve lifts the original left-invariant
flow through the actual native exponential. Actual manifold chain rules
and original global integral-curve uniqueness identify its exponential
with left multiplication. Time one gives an actual product logarithm. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_logarithmLift_integral (w u : E) :
    IsMIntegralCurve
      (fun t => nativeLieExponential (I := I) (G := G)
        (nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t))
      (mulInvariantVectorField (I := I) (G := G) w) := by
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  let γ : ℝ → E := nativeLieLogarithmLift (E := E) (I := I) (G := G) w u
  let F : E → E := nativeLieLogarithmVectorField (I := I) (G := G) w
  change IsMIntegralCurve (exp ∘ γ) (mulInvariantVectorField (I := I) (G := G) w)
  intro t
  have hd : MDifferentiableAt 𝓘(ℝ, E) I exp (γ t) :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (F (γ t))) :=
    (nativeLieLogarithmLift_hasDerivAt (I := I) (G := G) w u t).hasFDerivAt.hasMFDerivAt
  apply (hd.hasMFDerivAt.comp t hγ).congr_mfderiv
  change (mfderiv 𝓘(ℝ, E) I exp (γ t) : E →L[ℝ] E).comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight (F (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := I) (G := G) w (exp (γ t)) : E)
  apply ContinuousLinearMap.ext
  intro a
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I exp (γ t)
  let V : E := mulInvariantVectorField (I := I) (G := G) w (exp (γ t))
  change D (a • F (γ t)) = a • V
  have he : D (F (γ t)) = V := by
    have h := nativeLieExponential_mfderiv_apply (I := I) (G := G) (γ t) (F (γ t))
    change D (F (γ t)) = mulInvariantVectorField (I := I) (G := G)
      (nativeLieDexp (I := I) (G := G) (γ t) (F (γ t))) (exp (γ t)) at h
    have hF : nativeLieDexp (I := I) (G := G) (γ t) (F (γ t)) = w :=
      nativeLieLogarithmVectorField_dexp w (γ t)
    rw [hF] at h
    exact h
  rw [map_smul, he]

 theorem nativeLieExponential_logarithmLift (w u : E) (t : ℝ) :
    nativeLieExponential (I := I) (G := G)
        (nativeLieLogarithmLift (E := E) (I := I) (G := G) w u t) =
      nativeLieExponential (I := I) (G := G) u *
        lieOneParameterCurve (I := I) (G := G) w t := by
  let x : GroupLieAlgebra I G := w
  have h := lie_invariant_integralCurve_unique x
    (nativeLieExponential_logarithmLift_integral (I := I) (G := G) w u)
    (lie_invariant_integralCurve_left_translate x (lieOneParameterCurve_integral x)
      (nativeLieExponential (I := I) (G := G) u)) (t₀ := 0) (by
        simp only [nativeLieLogarithmLift_zero, lieOneParameterCurve_zero, mul_one])
  exact congrFun h t

 theorem nativeLieExponential_product_logarithm (u w : E) :
    nativeLieExponential (I := I) (G := G)
        (nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1) =
      nativeLieExponential (I := I) (G := G) u *
        nativeLieExponential (I := I) (G := G) w :=
  nativeLieExponential_logarithmLift w u 1

end Hindman168
