import Hindman168.NativeRationalCompactRelativePolynomial
import Hindman168.NativeRationalRelativeCharacterSplitting

/-! Exact actual relative scalar polynomial splits into the actual original
normalized diagonal scalar and the actual F_2-valued difference polynomial.
No extension of the difference character to the full original group is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalCompactDifferencePolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ) :
    RoughVectorMvPolynomial Unit (L.layer 2) :=
  roughVectorMvLinearMap (nativeRationalRelativeDifferenceCoordinate D L).toLinearMap
    (nativeRationalCompactRelativePolynomial D L p hp h)

theorem native_rational_compact_relative_second_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ) (x : Unit → ℝ) :
    (nativeRationalRelativeModelInclusion D L 1 (roughVectorMvEval (E := (nativeRationalRelativeData D L 1).E)
      (nativeRationalCompactRelativePolynomial D L p hp h) x)).2 =
    roughVectorMvEval (E := D.E) (nativeRationalCompactNormalizedPolynomial D p) x := by
  have he := native_rational_weighted_relative_polynomial_eval D L _
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) (nativeRationalShiftRepresentative D p h) h x
  rw [native_rational_weighted_ambient_pair_eval] at he
  exact congrArg Prod.snd he

theorem native_rational_compact_relative_scalar_splitting {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h) =
    roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
      (nativeRationalCompactNormalizedPolynomial D p) +
    roughVectorMvProjection (nativeRationalRelativeDifferenceCharacter D L χ).toLinearMap
      (nativeRationalCompactDifferencePolynomial D L p hp h) := by
  apply MvPolynomial.funext
  intro x
  rw [map_add,roughVectorMvProjection_eval,roughVectorMvProjection_eval,roughVectorMvProjection_eval,
    nativeRationalCompactDifferencePolynomial,roughVectorMvLinearMap_eval]
  have he := native_rational_relative_character_decomposition D L χ
    (roughVectorMvEval (E := (nativeRationalRelativeData D L 1).E)
      (nativeRationalCompactRelativePolynomial D L p hp h) x)
  change _ = _ at he
  have hs := native_rational_compact_relative_second_eval D L p hp h x
  change (roughVectorMvEval (E := (nativeRationalRelativeData D L 1).E)
    (nativeRationalCompactRelativePolynomial D L p hp h) x).val.2 = _ at hs
  rw [hs] at he
  exact he

theorem native_rational_compact_relative_coefficient_splitting {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (J : Unit →₀ ℕ) :
    MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h)) =
    MvPolynomial.coeff J (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
      (nativeRationalCompactNormalizedPolynomial D p)) +
    MvPolynomial.coeff J (roughVectorMvProjection (nativeRationalRelativeDifferenceCharacter D L χ).toLinearMap
      (nativeRationalCompactDifferencePolynomial D L p hp h)) := by
  rw [native_rational_compact_relative_scalar_splitting,MvPolynomial.coeff_add]

end Hindman168
