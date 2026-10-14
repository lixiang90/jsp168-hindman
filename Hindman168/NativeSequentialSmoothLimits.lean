import Hindman168.NativeSmoothFactorParameterization
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Local uniform C1 limits and ALL-index compact bounds for the ACTUAL
scaled left group product, in its genuine ORIGINAL global logarithmic
coordinates. Each sequence curve and the limiting group map are smooth.
The actual identity covers even zero lengths at finitely many indices. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSequentialSmoothLogCurve {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) : D.E :=
  nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
    (c n * nativeSequentialFactorsLeft D n (L n*b) as)

theorem native_sequential_smooth_curve_parameter_identity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) :
    nativeSequentialSmoothLogCurve D L c as n = fun b =>
      nativeSmoothBinomialFamilyLog D (fun i => (as.get i).order) (fun i => (as.get i).vector)
        (nativeSequentialSmoothParameter D L c as n) b := by
  funext b
  exact (congrArg (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G))
    (native_sequential_smooth_parameter_actual_product D L c as n b)).symm.trans
      (nativeLieGlobalLogarithm_exponential (E := D.E) (I := D.I) (G := D.G) _)

def NativeSequentialSmoothCurveLimit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) : Prop :=
  ∃ h : ℝ → D.E, ContDiff ℝ ∞ h ∧
    (∀ n, ContDiff ℝ ∞ (nativeSequentialSmoothLogCurve D L c as n)) ∧
    ContMDiff 𝓘(ℝ) D.I ∞ (fun b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (h b)) ∧
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (nativeSequentialSmoothLogCurve D L c as) h atTop K ∧
      TendstoUniformlyOn (fun n => deriv (nativeSequentialSmoothLogCurve D L c as n)) (deriv h) atTop K ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∀ b ∈ K, ‖nativeSequentialSmoothLogCurve D L c as n b‖ ≤ B ∧
        ‖deriv (nativeSequentialSmoothLogCurve D L c as n) b‖ ≤ B

theorem native_sequential_smooth_curve_limits {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D))
    (hCoeffs : ∀ a ∈ as, ∃ z : ℝ,
      Tendsto (fun n => (L n)^a.order * a.realCoefficient n) atTop (𝓝 z)) :
    NativeSequentialSmoothCurveLimit D L c as := by
  classical
  choose z hz using (fun i : Fin as.length => hCoeffs (as.get i) (List.get_mem as i))
  let theta : ℕ → NativeSmoothBinomialParameter D as.length := nativeSequentialSmoothParameter D L c as
  let a : NativeSmoothBinomialParameter D as.length :=
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,0,z)
  let F : NativeSmoothBinomialParameter D as.length × ℝ → D.E := fun p =>
    nativeSmoothBinomialFamilyLog D (fun i => (as.get i).order) (fun i => (as.get i).vector) p.1 p.2
  have hF : ContDiff ℝ ∞ F := native_smooth_binomial_family_contDiff D _ _
  have htheta : Tendsto theta atTop (𝓝 a) := native_sequential_smooth_parameter_limit D L hL c cLimit hc as z hz
  let h : ℝ → D.E := fun b => F (a,b)
  have hh : ContDiff ℝ ∞ h := hF.comp (contDiff_const.prodMk contDiff_id)
  have he (n : ℕ) : nativeSequentialSmoothLogCurve D L c as n = (fun b => F (theta n,b)) :=
    native_sequential_smooth_curve_parameter_identity D L c as n
  refine ⟨h,hh,?_,?_,?_⟩
  · intro n
    rw [he n]
    exact hF.comp (contDiff_const.prodMk contDiff_id)
  · exact (nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp hh.contMDiff
  · intro K hK
    have hlim := smooth_parameter_compact_C1_limits F hF theta a htheta K hK
    have hbound := smooth_parameter_compact_C1_bounds F hF theta a htheta K hK
    have heFunctions : nativeSequentialSmoothLogCurve D L c as = (fun n b => F (theta n,b)) := funext he
    refine ⟨?_,?_,?_⟩
    · rw [heFunctions]
      exact hlim.1
    · simp only [heFunctions]
      exact hlim.2
    · obtain ⟨B,hB,hBounds⟩ := hbound
      refine ⟨B,hB,?_⟩
      intro n b hb
      rw [he n]
      exact hBounds n b hb

end Hindman168
