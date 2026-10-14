import Hindman168.NativeRationalScalarDifferencePolynomial
import Hindman168.NativeRationalCompactRelativePolynomial

/-! The COMPLETE scalar formula applies to the SAME actual compact
relative polynomial used by dense common-character extraction. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_compact_scalar_difference_polynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (h : ℤ) :
    let p₀ := nativeRationalCompactNormalizedPolynomial D p
    let hp₀ := native_rational_compact_normalized_polynomial_weighted D L hp
    let h₀ := native_rational_compact_normalized_polynomial_zero D p
    roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h) =
      roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p₀ +
      mvScalarTranslation (nativeRationalNonlinearScalar D L p₀ hp₀ h₀ χ) (fun _ => (h : ℝ)) -
      nativeRationalNonlinearScalar D L p₀ hp₀ h₀ χ +
      MvPolynomial.C (nativeRationalRelativeCommutatorValue D L χ
        (nativeIntegerLogPolynomialSequence D p₀ 1) (nativeRationalShiftRepresentative D p h))*MvPolynomial.X () :=
  native_rational_relative_scalar_difference_polynomial D L
    (nativeRationalCompactNormalizedPolynomial D p)
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) χ hχ (nativeRationalShiftRepresentative D p h) h

end Hindman168
