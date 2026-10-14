import Hindman168.LieOneParameterVelocity

/-! Actual native exponentials commute with genuinely differentiable group
homomorphisms. The original homomorphism law and native chain rule prove
intertwining of invariant fields; uniqueness of the constructed global
curves then proves the exponential comparison. No supplied exponential,
Lie embedding, or compatibility identity is used. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K]
  [LieGroup J (minSmoothness ℝ 3) K]

 theorem lie_hom_derivative_invariant_field (f : G →* K)
    (hf : MDifferentiable I J (f : G → K)) (v : GroupLieAlgebra I G) (g : G) :
    mfderiv I J (f : G → K) g (mulInvariantVectorField v g) =
      mulInvariantVectorField (I := J) (G := K)
        (mfderiv I J (f : G → K) (1 : G) v) (f g) := by
  have hn : minSmoothness ℝ 3 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness).ne'
  have hg : MDifferentiableAt I I (fun x : G => g * x) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  have hfg : MDifferentiableAt J J (fun x : K => f g * x) (1 : K) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hn
  have h1 := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := J)
    (1 : G) (hf g) hg (mul_one g) v
  have h2 := mfderiv_comp_apply_of_eq (I := I) (I' := J) (I'' := J)
    (1 : G) hfg (hf 1) f.map_one v
  have heq : (f : G → K) ∘ (fun x : G => g * x) =
      (fun x : K => f g * x) ∘ (f : G → K) :=
    funext fun x => f.map_mul g x
  rw [heq] at h1
  exact h1.symm.trans h2

 theorem lie_hom_integralCurve_map (f : G →* K)
    (hf : MDifferentiable I J (f : G → K)) (v : GroupLieAlgebra I G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) :
    IsMIntegralCurve ((f : G → K) ∘ γ)
      (mulInvariantVectorField (I := J) (G := K)
        (mfderiv I J (f : G → K) (1 : G) v)) := by
  intro t
  apply ((hf (γ t)).hasMFDerivAt.comp t (hγ t)).congr_mfderiv
  change (mfderiv I J (f : G → K) (γ t) : E →L[ℝ] F).comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t) : E)) =
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (mulInvariantVectorField (I := J) (G := K)
        (mfderiv I J (f : G → K) (1 : G) v) (f (γ t)) : F)
  apply ContinuousLinearMap.ext
  intro a
  change (mfderiv I J (f : G → K) (γ t) : E →L[ℝ] F)
    (a • (mulInvariantVectorField v (γ t) : E)) =
    a • (mulInvariantVectorField (I := J) (G := K)
      (mfderiv I J (f : G → K) (1 : G) v) (f (γ t)) : F)
  rw [map_smul]
  erw [lie_hom_derivative_invariant_field f hf v (γ t)]

variable [CompleteSpace E] [BoundarylessManifold I G] [T2Space G]
  [CompleteSpace F] [BoundarylessManifold J K] [T2Space K]

 theorem lie_hom_oneParameterCurve_map (f : G →* K)
    (hf : MDifferentiable I J (f : G → K)) (v : GroupLieAlgebra I G) :
    (f : G → K) ∘ lieOneParameterCurve v =
      lieOneParameterCurve (I := J) (G := K)
        (mfderiv I J (f : G → K) (1 : G) v) := by
  apply lieOneParameterCurve_unique
    (mfderiv I J (f : G → K) (1 : G) v)
    (lie_hom_integralCurve_map f hf v (lieOneParameterCurve_integral v))
  change f (lieOneParameterCurve v 0) = 1
  rw [lieOneParameterCurve_zero, f.map_one]

 theorem nativeLieExponential_map (f : G →* K)
    (hf : MDifferentiable I J (f : G → K)) (v : GroupLieAlgebra I G) :
    f (nativeLieExponential v) = nativeLieExponential (I := J) (G := K)
      (mfderiv I J (f : G → K) (1 : G) v) :=
  congrFun (lie_hom_oneParameterCurve_map f hf v) 1

end Hindman168
