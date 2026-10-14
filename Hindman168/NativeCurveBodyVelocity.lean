import Hindman168.NativeSequentialSmoothLimits
import Hindman168.NativeLieLogarithmVectorField
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! ACTUAL left-trivialized velocities of native group curves. For a
smooth logarithmic curve the manifold chain rule identifies this genuine
velocity with the original dexp operator applied to its real derivative. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCurveBodyVelocity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g : ℝ → D.G) (b : ℝ) : D.E :=
  mfderiv D.I D.I (fun x : D.G => (g b)⁻¹*x) (g b)
    (mfderiv 𝓘(ℝ) D.I g b (1 : ℝ))

theorem native_curve_body_velocity_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (h : ℝ → D.E) (hh : ContDiff ℝ ∞ h) (b : ℝ) :
    nativeCurveBodyVelocity D (fun r => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (h r)) b =
      nativeLieDexp (E := D.E) (I := D.I) (G := D.G) (h b) (deriv h b) := by
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  have hexp : MDifferentiableAt 𝓘(ℝ, D.E) D.I exp (h b) :=
    (nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).mdifferentiableAt (by norm_num)
  have hreal : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, D.E) h b :=
    hh.contMDiff.mdifferentiableAt (by norm_num)
  have he := mfderiv_comp b hexp hreal
  have h1 := congrArg (fun A : ℝ →L[ℝ] D.E =>
    mfderiv D.I D.I (fun x : D.G => (exp (h b))⁻¹*x) (exp (h b)) (A 1)) he
  change nativeCurveBodyVelocity D (fun r => exp (h r)) b = _ at h1
  rw [mfderiv_eq_fderiv] at h1
  exact h1

theorem native_dexp_joint_contDiff {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    ContDiff ℝ ∞ (fun p : D.E × D.E => nativeLieDexp (E := D.E) (I := D.I) (G := D.G) p.1 p.2) :=
  ((nativeLieDexp_contDiff (E := D.E) (I := D.I) (G := D.G)).comp contDiff_fst).clm_apply contDiff_snd

theorem native_dexp_contDiff_comp {s : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : NativeNilmanifoldData.{u} s) (v w : X → D.E)
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => nativeLieDexp (E := D.E) (I := D.I) (G := D.G) (v x) (w x)) :=
  ((nativeLieDexp_contDiff (E := D.E) (I := D.I) (G := D.G)).comp hv).clm_apply hw

end Hindman168
