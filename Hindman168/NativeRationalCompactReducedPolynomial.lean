import Hindman168.NativeRationalCompactNormalizedPairSamples
import Hindman168.NativeRationalWeightedDegreeReducedPolynomial
import Hindman168.RoughVectorZeroTrimProjection

/-! Actual compact normalization followed by true weighted relative/terminal
reduction supplies an actual polynomial at the next IMAGE filtration stage. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalCompactReducedPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h : ℤ) :
    RoughVectorMvPolynomial Unit (nativeRationalDegreeReducedData D F).E :=
  roughVectorMvZeroTrim (nativeRationalWeightedDegreeReducedPolynomial D F
    (nativeRationalCompactNormalizedPolynomial D p) (native_rational_compact_normalized_polynomial_weighted D F hp)
    (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h)

theorem native_rational_compact_reduced_polynomial_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeDegreeReducedRationalLieFiltration D F).layer
      (nativeRationalCompactReducedPolynomial D F p hp h) 0 :=
  rough_vector_zero_trim_weighted _ (native_rational_weighted_degree_reduced_polynomial_weighted D F
    _ (native_rational_compact_normalized_polynomial_weighted D F hp)
    (native_rational_compact_normalized_polynomial_zero D p) _ h)

theorem native_rational_compact_reduced_polynomial_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h : ℤ) :
    RoughVectorMvDegreeLE (nativeRationalCompactReducedPolynomial D F p hp h) (ℓ-1) :=
  native_rational_weighted_degree_reduced_polynomial_degree_drop D F _
    (native_rational_compact_normalized_polynomial_weighted D F hp)
    (native_rational_compact_normalized_polynomial_zero D p) _ h

theorem native_rational_compact_reduced_polynomial_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ) :
    nativeIntegerLogPolynomialSequence (nativeRationalDegreeReducedData D F)
      (nativeRationalCompactReducedPolynomial D F p hp h) n =
    nativeRationalTerminalGroupProjection (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
      (nativeRationalCompactNormalizedIntegerPair D F p hp h n) := by
  change nativeLieExponential (E := (nativeRationalDegreeReducedData D F).E)
    (I := (nativeRationalDegreeReducedData D F).I) (G := (nativeRationalDegreeReducedData D F).G)
    (roughVectorMvEval (E := (nativeRationalDegreeReducedData D F).E)
      (roughVectorMvZeroTrim (nativeRationalWeightedDegreeReducedPolynomial D F
        (nativeRationalCompactNormalizedPolynomial D p) (native_rational_compact_normalized_polynomial_weighted D F hp)
        (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h))
      (fun _ => (n : ℝ))) = _
  rw [rough_vector_zero_trim_eval]
  exact native_rational_weighted_degree_reduced_polynomial_exponential D F _
    (native_rational_compact_normalized_polynomial_weighted D F hp)
    (native_rational_compact_normalized_polynomial_zero D p) _ h n

theorem native_rational_compact_reduced_polynomial_sample {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h n : ℤ) :
    nativeMvPolynomialOrbit (nativeRationalDegreeReducedData D F)
      (nativeRationalCompactReducedPolynomial D F p hp h) (fun _ => n) =
    nativeRationalTerminalFactorMap (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
      ((nativeRationalCompactNormalizedIntegerPair D F p hp h n) :
        (nativeRationalRelativeData D F 1).G ⧸ (nativeRationalRelativeData D F 1).Γ) := by
  change ((nativeIntegerLogPolynomialSequence (nativeRationalDegreeReducedData D F)
    (nativeRationalCompactReducedPolynomial D F p hp h) n) :
    (nativeRationalDegreeReducedData D F).G ⧸ (nativeRationalDegreeReducedData D F).Γ) = _
  rw [native_rational_compact_reduced_polynomial_exponential]
  rfl

theorem native_rational_compact_reduced_polynomial_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h : ℤ)
    (χ : (nativeRationalDegreeReducedData D F).E →ₗ[ℝ] ℝ) :
    roughVectorMvProjection χ (nativeRationalCompactReducedPolynomial D F p hp h) =
      roughVectorMvProjection (χ.comp (nativeRationalTerminalModelProjection (nativeRationalRelativeData D F 1)
        (nativeRelativeRationalLieFiltration D F)).toLinearMap)
        (nativeRationalWeightedRelativePolynomial D F (nativeRationalCompactNormalizedPolynomial D p)
          (native_rational_compact_normalized_polynomial_weighted D F hp)
          (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h) :=
  (rough_vector_zero_trim_projection χ _).trans
    (native_rational_weighted_degree_reduced_polynomial_scalar D F _
      (native_rational_compact_normalized_polynomial_weighted D F hp)
      (native_rational_compact_normalized_polynomial_zero D p) _ h χ)

theorem native_rational_compact_reduced_polynomial_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (h : ℤ) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeRationalCompactReducedPolynomial D F p hp h) J =
      nativeRationalTerminalModelProjection (nativeRationalRelativeData D F 1) (nativeRelativeRationalLieFiltration D F)
        (roughVectorMvCoefficient
          (nativeRationalWeightedRelativePolynomial D F (nativeRationalCompactNormalizedPolynomial D p)
            (native_rational_compact_normalized_polynomial_weighted D F hp)
            (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h) J) :=
  (rough_vector_zero_trim_coefficient _ J).trans (rough_vector_coefficient_linear_map _ _ J)

end Hindman168
