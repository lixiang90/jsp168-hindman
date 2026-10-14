import Hindman168.NativeRationalCompactReducedPolynomial
import Hindman168.NativeRationalTerminalCharacterPolynomial

/-! Actual compact-normalized relative polynomial, its true weights and exact
scalar/monomial/binomial transport from the actual terminal quotient. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalCompactRelativePolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ) :
    RoughVectorMvPolynomial Unit (nativeRationalRelativeData D L 1).E :=
  nativeRationalWeightedRelativePolynomial D L (nativeRationalCompactNormalizedPolynomial D p)
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h

theorem native_rational_compact_relative_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeRelativeRationalLieFiltration D L).layer
      (nativeRationalCompactRelativePolynomial D L p hp h) 0 :=
  native_rational_weighted_relative_polynomial_weighted D L _
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) _ h

theorem native_rational_compact_relative_polynomial_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ) :
    nativeRationalCompactReducedPolynomial D L p hp h =
      roughVectorMvZeroTrim (nativeRationalTerminalPolynomial (nativeRationalRelativeData D L 1)
        (nativeRelativeRationalLieFiltration D L) (nativeRationalCompactRelativePolynomial D L p hp h)) := rfl

theorem native_rational_compact_relative_character_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
    (χ : (nativeRationalDegreeReducedData D L).E →L[ℝ] ℝ) :
    roughVectorMvProjection (nativeRationalTerminalCharacterPullback (nativeRationalRelativeData D L 1)
      (nativeRelativeRationalLieFiltration D L) χ).toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h) =
    roughVectorMvProjection χ.toLinearMap (nativeRationalCompactReducedPolynomial D L p hp h) := by
  have he := native_rational_terminal_character_pullback_zero_trim_scalar (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) χ (nativeRationalCompactRelativePolynomial D L p hp h)
  exact he

theorem native_rational_compact_relative_character_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
    (χ : (nativeRationalDegreeReducedData D L).E →L[ℝ] ℝ) (J : Unit →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection (nativeRationalTerminalCharacterPullback
      (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) χ).toLinearMap
        (nativeRationalCompactRelativePolynomial D L p hp h)) =
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactReducedPolynomial D L p hp h)) := by
  rw [native_rational_compact_relative_character_scalar]

theorem native_rational_compact_relative_character_binomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
    (χ : (nativeRationalDegreeReducedData D L).E →L[ℝ] ℝ) (J : Unit → ℕ) :
    mvPolynomialBinomialCoefficient (roughVectorMvProjection (nativeRationalTerminalCharacterPullback
      (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L) χ).toLinearMap
        (nativeRationalCompactRelativePolynomial D L p hp h)) ℓ J =
    mvPolynomialBinomialCoefficient (roughVectorMvProjection χ.toLinearMap
      (nativeRationalCompactReducedPolynomial D L p hp h)) (ℓ-1) J := by
  have he := native_rational_terminal_character_pullback_binomial (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) χ (native_rational_compact_relative_polynomial_weighted D L p hp h) J
  exact he

end Hindman168
