import Hindman168.NativeBasepointRelativeIntegerPair
import Hindman168.NativeBasepointPolynomialSamples
import Hindman168.NativeTerminalRelativePairObservable

/-! GENERAL original starting values and actual linear-shift lattice
representatives retain EXACT original terminal Fourier derivative samples
on the SAME native relative group and SAME original stretch. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_terminal_original_sample {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial σ D.E) (r : D.G) (γ : D.Γ)
    (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ)
    (k : nativeOriginalTerminalIndex D d → ℤ) (x : σ → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeOriginalTerminalFourierProjection D d hd k (nativeBasepointObservable D r F)
        (nativeMvPolynomialOrbit D (nativeBasepointPolynomial D p r) x) =
      nativeOriginalTerminalFourierProjection D d hd k F (nativeMvPolynomialOrbit D p x) := by
  intro F
  rw [native_basepoint_observable_terminal_projection,native_basepoint_observable_apply,
    native_basepoint_polynomial_original_orbit D p r γ hr]

theorem native_basepoint_terminal_pair_original_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (γ0 γh : D.Γ)
    (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ0)
    (k : nativeOriginalTerminalIndex D d → ℤ) (h n : ℤ)
    (ht : nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h = t * γh) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeTerminalRelativePairObservable D d hd k t (nativeBasepointObservable D r F)
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) =
      nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
      star (nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_terminal_relative_pair_observable_apply,native_terminal_product_pair_observable_apply]
  change nativeOriginalTerminalFourierProjection D d hd k (nativeBasepointObservable D r F)
      (t • ((roughNormalizedIntegerPair
        (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n).1 : D.G ⧸ D.Γ)) *
    star (nativeOriginalTerminalFourierProjection D d hd k (nativeBasepointObservable D r F)
      ((roughNormalizedIntegerPair
        (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n).2 : D.G ⧸ D.Γ)) = _
  have hfirst : t • ((roughNormalizedIntegerPair
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n).1 : D.G ⧸ D.Γ) =
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) (n+h) : D.G ⧸ D.Γ) :=
    rough_normalized_integer_pair_original_coset D.Γ
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n γh ht
  rw [hfirst,rough_normalized_integer_pair_second]
  exact congrArg₂ (fun a b : ℂ => a * star b)
    (native_basepoint_terminal_original_sample D d hd p r γ0 hr k (fun _ => n+h) F)
    (native_basepoint_terminal_original_sample D d hd p r γ0 hr k (fun _ => n) F)

theorem native_basepoint_terminal_pair_original_mean {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (γ0 γh : D.Γ)
    (hr : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p 0) = r * γ0)
    (k : nativeOriginalTerminalIndex D d → ℤ) (h : ℤ) (a : Finset ℤ)
    (ht : nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 1 ^ h = t * γh) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      finiteComplexSetMean a (fun n => nativeTerminalRelativePairObservable D d hd k t (nativeBasepointObservable D r F)
        (nativeBasepointRelativeIntegerPair D d hd p hp r t h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) =
      finiteComplexSetMean a (fun n => nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
        star (nativeOriginalTerminalFourierProjection D d hd k F
          (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ))) := by
  intro F
  apply congrArg (finiteComplexSetMean a)
  funext n
  exact native_basepoint_terminal_pair_original_sample D d hd p hp r t γ0 γh hr k h n ht F

end Hindman168
