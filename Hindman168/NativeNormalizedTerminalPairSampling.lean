import Hindman168.NativeNormalizedIntegerPair
import Hindman168.NativeTerminalRelativePairObservable

/-! The ACTUAL normalized relative pair retains exactly the original
terminal Fourier shifted/unshifted derivative samples. Original lattice
normality is not used. Relative polynomial filtered degree remains open. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_normalized_terminal_pair_original_sample {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0)
    (k : nativeOriginalTerminalIndex D d → ℤ) (r : D.G) (h n : ℤ)
    (γ : D.Γ) (hr : nativeIntegerLogPolynomialSequence D p 1 ^ h = r * γ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      nativeTerminalRelativePairObservable D d hd k r F
        (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ) =
      nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
      star (nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  rw [native_terminal_relative_pair_observable_apply,native_terminal_product_pair_observable_apply]
  change nativeOriginalTerminalFourierProjection D d hd k F
      (r • ((roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n).1 : D.G ⧸ D.Γ)) *
    star (nativeOriginalTerminalFourierProjection D d hd k F
      ((roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n).2 : D.G ⧸ D.Γ)) = _
  have hfirst : r • ((roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n).1 : D.G ⧸ D.Γ) =
      (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) :=
    rough_normalized_integer_pair_original_coset D.Γ (nativeIntegerLogPolynomialSequence D p) r h n γ hr
  rw [hfirst,rough_normalized_integer_pair_second]

theorem native_normalized_terminal_pair_original_mean {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0)
    (k : nativeOriginalTerminalIndex D d → ℤ) (r : D.G) (h : ℤ) (a : Finset ℤ)
    (γ : D.Γ) (hr : nativeIntegerLogPolynomialSequence D p 1 ^ h = r * γ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      finiteComplexSetMean a (fun n => nativeTerminalRelativePairObservable D d hd k r F
        (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n :
          (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ)) =
      finiteComplexSetMean a (fun n => nativeOriginalTerminalFourierProjection D d hd k F
        (nativeIntegerLogPolynomialSequence D p (n+h) : D.G ⧸ D.Γ) *
        star (nativeOriginalTerminalFourierProjection D d hd k F
          (nativeIntegerLogPolynomialSequence D p n : D.G ⧸ D.Γ))) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  apply congrArg (finiteComplexSetMean a)
  funext n
  exact native_normalized_terminal_pair_original_sample D d hd p hp h0 k r h n γ hr F

end Hindman168
