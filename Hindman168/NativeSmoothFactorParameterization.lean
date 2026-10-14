import Hindman168.NativeSmoothBinomialFamily
import Hindman168.SmoothParameterUniformLimits

/-! The finite-dimensional parameters are the ACTUAL compact constants,
inverse lengths and scaled correction coefficients. Their native family is
exactly the SAME ordered original left product at L*beta, not a replacement
sequence with similar coefficients. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSequentialSmoothParameter {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) : NativeSmoothBinomialParameter D as.length :=
  (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (c n),
    (L n)⁻¹,fun i => (L n)^(as.get i).order * (as.get i).realCoefficient n)

theorem native_sequential_smooth_parameter_limit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D)) (z : Fin as.length → ℝ)
    (hz : ∀ i, Tendsto (fun n => (L n)^(as.get i).order * (as.get i).realCoefficient n) atTop (𝓝 (z i))) :
    Tendsto (nativeSequentialSmoothParameter D L c as) atTop
      (𝓝 (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,(0 : ℝ),z)) := by
  change Tendsto (fun n => nativeSequentialSmoothParameter D L c as n) atTop
    (𝓝 (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,(0 : ℝ),z))
  simpa only [nativeSequentialSmoothParameter, Function.comp_def, Pi.inv_apply] using
    (((nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)).continuous.tendsto cLimit).comp hc).prodMk_nhds
      (hL.inv_tendsto_atTop.prodMk_nhds (tendsto_pi_nhds.mpr hz))

theorem native_sequential_factors_left_list {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) :
    nativeSequentialFactorsLeft D n b as = (as.map (fun a => nativeSequentialFactorLeft D a n b)).prod := by
  induction as with
  | nil => rfl
  | cons a as ih => exact congrArg (fun g : D.G => nativeSequentialFactorLeft D a n b * g) ih

theorem native_sequential_smooth_parameter_actual_product {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeSmoothBinomialFamilyLog D (fun i => (as.get i).order) (fun i => (as.get i).vector)
        (nativeSequentialSmoothParameter D L c as n) b) =
      c n * nativeSequentialFactorsLeft D n (L n * b) as := by
  have he := native_smooth_binomial_family_exponential D (fun i => (as.get i).order)
    (fun i => (as.get i).vector) (nativeSequentialSmoothParameter D L c as n) b
  have hScalar (i : Fin as.length) : scaledBinomialSmooth (as.get i).order
      ((L n)^(as.get i).order * (as.get i).realCoefficient n) (L n)⁻¹ b =
      (as.get i).realCoefficient n * MvPolynomial.eval (fun _ => L n*b) (adaptedTaylorBinomial (as.get i).order) :=
    (scaled_binomial_smooth_identity_all_lengths (as.get i).order ((as.get i).realCoefficient n) (L n) b).symm
  have hFunctions : (fun i : Fin as.length => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (scaledBinomialSmooth (as.get i).order ((L n)^(as.get i).order * (as.get i).realCoefficient n)
        (L n)⁻¹ b • (as.get i).vector)) =
      (fun i : Fin as.length => nativeSequentialFactorLeft D (as.get i) n (L n*b)) := by
    funext i
    exact congrArg (fun r : ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (r • (as.get i).vector)) (hScalar i)
  have hList : List.ofFn (fun i : Fin as.length => nativeSequentialFactorLeft D (as.get i) n (L n*b)) =
      as.map (fun a => nativeSequentialFactorLeft D a n (L n*b)) := by
    exact (List.ofFn_comp' as.get (fun a => nativeSequentialFactorLeft D a n (L n*b))).trans
      (congrArg (List.map (fun a => nativeSequentialFactorLeft D a n (L n*b))) (List.ofFn_get as))
  have hprod := congrArg (fun f : Fin as.length → D.G => (List.ofFn f).prod) hFunctions
  have hprod' := hprod.trans (congrArg List.prod hList)
  have hc : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (c n)) = c n :=
    nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) (c n)
  exact he.trans ((congrArg₂ (fun g h : D.G => g*h) hc hprod').trans
    (congrArg (fun g : D.G => c n*g) (native_sequential_factors_left_list D as n (L n*b)).symm))

end Hindman168
