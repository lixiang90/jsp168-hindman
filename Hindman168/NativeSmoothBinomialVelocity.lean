import Hindman168.NativeCurveBodyVelocity

/-! The genuine left-trivialized derivative is a smooth finite-dimensional
parameter family too. It is exactly the ACTUAL original group-curve velocity
at every sequence index, not merely the derivative of a substitute function. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSmoothBinomialFamilyVelocity {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E)
    (theta : NativeSmoothBinomialParameter D N) (b : ℝ) : D.E :=
  nativeLieDexp (E := D.E) (I := D.I) (G := D.G)
    (nativeSmoothBinomialFamilyLog D order vector theta b)
    (smoothParameterCurveDerivative (fun p : NativeSmoothBinomialParameter D N × ℝ =>
      nativeSmoothBinomialFamilyLog D order vector p.1 p.2) theta b)

theorem native_smooth_binomial_velocity_contDiff {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E) :
    ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ =>
      nativeSmoothBinomialFamilyVelocity D order vector p.1 p.2) := by
  let F : NativeSmoothBinomialParameter D N × ℝ → D.E := fun p =>
    nativeSmoothBinomialFamilyLog D order vector p.1 p.2
  have hF : ContDiff ℝ ∞ F := native_smooth_binomial_family_contDiff D order vector
  have hV : ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ =>
      smoothParameterCurveDerivative F p.1 p.2) := smooth_parameter_curve_derivative_contDiff F hF
  exact native_dexp_contDiff_comp D F _ hF hV

noncomputable def nativeSequentialSmoothGroupCurve {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) : D.G :=
  c n * nativeSequentialFactorsLeft D n (L n*b) as

theorem native_sequential_body_velocity_parameter_identity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) :
    nativeCurveBodyVelocity D (nativeSequentialSmoothGroupCurve D L c as n) = fun b =>
      nativeSmoothBinomialFamilyVelocity D (fun i => (as.get i).order) (fun i => (as.get i).vector)
        (nativeSequentialSmoothParameter D L c as n) b := by
  let h : ℝ → D.E := fun b => nativeSmoothBinomialFamilyLog D
    (fun i => (as.get i).order) (fun i => (as.get i).vector) (nativeSequentialSmoothParameter D L c as n) b
  have hh : ContDiff ℝ ∞ h := (native_smooth_binomial_family_contDiff D _ _).comp
    (contDiff_const.prodMk contDiff_id)
  have hg : nativeSequentialSmoothGroupCurve D L c as n = fun b =>
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (h b) :=
    funext (fun b => (native_sequential_smooth_parameter_actual_product D L c as n b).symm)
  have hv := funext (fun b => native_curve_body_velocity_exponential D h hh b)
  exact (congrArg (nativeCurveBodyVelocity D) hg).trans hv

end Hindman168
