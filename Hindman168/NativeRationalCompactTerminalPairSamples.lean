import Hindman168.NativeRationalBasepointTerminalProjection
import Hindman168.NativeRationalCompactReducedPolynomial
import Hindman168.NativeRationalTerminalRelativePairObservable

/-! Exact original Fourier derivative samples after both actual compact
normalizations. No bound on the original coefficients or lattice logarithms. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_compact_terminal_pair_original_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : nativeRationalTerminalIndex D L → ℤ) (h n : ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      nativeRationalTerminalRelativePairObservable D L k (nativeRationalShiftRepresentative D p h)
        (nativeBasepointObservable D (nativeRationalBasepointRepresentative D p) H)
        ((nativeRationalCompactNormalizedIntegerPair D L p hp h n) :
          (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ) =
      nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
        star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n))) := by
  intro H
  rw [native_rational_terminal_relative_pair_observable_apply,
    native_rational_terminal_product_pair_observable_apply,
    native_rational_basepoint_observable_terminal_projection]
  simp only [native_basepoint_observable_apply,← mul_smul]
  exact native_rational_compact_pair_original_observable_sample D L p hp h n
    (nativeRationalTerminalFourierProjection D L k H)

theorem native_rational_compact_terminal_pair_original_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : nativeRationalTerminalIndex D L → ℤ) (h : ℤ) (a : Finset ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ H : C(D.G ⧸ D.Γ,ℂ),
      finiteComplexSetMean a (fun n => nativeRationalTerminalRelativePairObservable D L k
        (nativeRationalShiftRepresentative D p h)
        (nativeBasepointObservable D (nativeRationalBasepointRepresentative D p) H)
        ((nativeRationalCompactNormalizedIntegerPair D L p hp h n) :
          (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ)) =
      finiteComplexSetMean a (fun n =>
        nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n+h)) *
          star (nativeRationalTerminalFourierProjection D L k H (nativeMvPolynomialOrbit D p (fun _ => n)))) := by
  intro H
  apply congrArg (finiteComplexSetMean a)
  funext n
  exact native_rational_compact_terminal_pair_original_sample D L p hp k h n H

end Hindman168
