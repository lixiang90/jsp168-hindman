import Hindman168.NativeSmoothProductLog
import Hindman168.ScaledBinomialSmooth

/-! A finite-dimensional smooth parameter family for the ACTUAL ordered
left factors, in the ORIGINAL native logarithmic coordinates. The inverse
length is a genuine parameter, including its limiting value zero. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

abbrev NativeSmoothBinomialParameter {s : ℕ} (D : NativeNilmanifoldData.{u} s) (N : ℕ) :=
  D.E × (ℝ × (Fin N → ℝ))

noncomputable def nativeSmoothBinomialFamilyLog {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E)
    (theta : NativeSmoothBinomialParameter D N) (b : ℝ) : D.E :=
  nativeSmoothProductLog D theta.1 (nativeSmoothOrderedLog D (List.ofFn (fun i =>
    scaledBinomialSmooth (order i) (theta.2.2 i) theta.2.1 b • vector i)))

theorem native_smooth_binomial_family_contDiff {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E) :
    ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ =>
      nativeSmoothBinomialFamilyLog D order vector p.1 p.2) := by
  have hz (i : Fin N) : ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ => p.1.2.2 i) :=
    (contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
  have ht : ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ => p.1.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  have hv (i : Fin N) : ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ =>
      scaledBinomialSmooth (order i) (p.1.2.2 i) p.1.2.1 p.2 • vector i) :=
    (scaled_binomial_smooth_contDiff (order i) _ _ _ (hz i) ht contDiff_snd).smul contDiff_const
  have hp := native_smooth_ordered_log_contDiff D N
    (fun i (p : NativeSmoothBinomialParameter D N × ℝ) =>
      scaledBinomialSmooth (order i) (p.1.2.2 i) p.1.2.1 p.2 • vector i) hv
  have hc : ContDiff ℝ ∞ (fun p : NativeSmoothBinomialParameter D N × ℝ => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  exact (native_smooth_product_log_contDiff D).comp (hc.prodMk hp)

theorem native_smooth_binomial_family_exponential {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E)
    (theta : NativeSmoothBinomialParameter D N) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeSmoothBinomialFamilyLog D order vector theta b) =
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) theta.1 *
        (List.ofFn (fun i => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (scaledBinomialSmooth (order i) (theta.2.2 i) theta.2.1 b • vector i))).prod := by
  have he := nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G)
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) theta.1 *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (nativeSmoothOrderedLog D (List.ofFn (fun i =>
          scaledBinomialSmooth (order i) (theta.2.2 i) theta.2.1 b • vector i))))
  have hprod := native_smooth_ordered_log_exponential D (List.ofFn (fun i =>
    scaledBinomialSmooth (order i) (theta.2.2 i) theta.2.1 b • vector i))
  have h := he.trans (congrArg (fun g : D.G => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) theta.1 * g) hprod)
  simpa only [nativeSmoothBinomialFamilyLog, nativeSmoothProductLog, List.map_ofFn, Function.comp_def] using h

end Hindman168
