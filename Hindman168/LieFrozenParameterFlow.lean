import Hindman168.LieInvariantParameterField
import Hindman168.LieOneParameterExponential

/-! The parameter is a genuine frozen coordinate of an actual vector
field on E × G. Its integral curves are the original native exponential
curves, with their tangent parameter unchanged. -/

namespace Hindman168
open Bundle Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]

 noncomputable def lieFrozenParameterField (p : E × G) :
    TangentSpace (𝓘(ℝ, E).prod I) p :=
  (0, mulInvariantVectorField (I := I) p.1 p.2)

 theorem lieFrozenParameterField_contMDiff_one :
    ContMDiff (𝓘(ℝ, E).prod I) (𝓘(ℝ, E).prod I).tangent 1
      (fun p : E × G => (⟨p, lieFrozenParameterField (I := I) p⟩ :
        TangentBundle (𝓘(ℝ, E).prod I) (E × G))) := by
  have h₁ : ContMDiff (𝓘(ℝ, E).prod I) 𝓘(ℝ, E).tangent 1
      (fun p : E × G => (⟨p.1, 0⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (contMDiff_zeroSection _ _).comp contMDiff_fst
  have h := contMDiff_equivTangentBundleProd_symm.comp
    (h₁.prodMk (lie_invariant_field_joint_contMDiff_one (I := I) (G := G)))
  convert! h

variable [CompleteSpace E] [BoundarylessManifold I G] [T2Space G]

 theorem lieFrozenParameterCurve_integral (v : E) :
    IsMIntegralCurve (I := 𝓘(ℝ, E).prod I)
      (fun t => (v, lieOneParameterCurve (I := I) (G := G) v t))
      (lieFrozenParameterField (I := I)) := by
  intro t
  have hd := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, E)) v t).prodMk (lieOneParameterCurve_integral (I := I) (G := G) v t)
  apply hd.congr_mfderiv
  change (0 : ℝ →L[ℝ] E).prod
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := I) v (lieOneParameterCurve v t) : E)) =
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (0, (mulInvariantVectorField (I := I) v (lieOneParameterCurve v t) : E))
  ext <;> simp

end Hindman168
