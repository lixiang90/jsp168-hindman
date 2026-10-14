import Hindman168.NativeRationalCompactUnivariateScalars

/-! Actual compact diagonal P has TRUE degree, zero at origin and SAME
original group value at one; EVERY combined coefficient bound transports. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_compact_diagonal_scalar_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    (nativeRationalCompactDiagonalScalar D L p χ).natDegree ≤ ℓ :=
  scalar_unit_polynomial_degree _ ℓ (roughVectorMvProjection_degree _
    (native_rational_compact_normalized_polynomial_degree D L hp))

theorem native_rational_compact_diagonal_scalar_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    (nativeRationalCompactDiagonalScalar D L p χ).eval 0=0 := by
  rw [nativeRationalCompactDiagonalScalar,scalar_unit_polynomial_eval,roughVectorMvProjection_eval,
    native_rational_compact_normalized_polynomial_zero,map_zero]

theorem native_rational_compact_diagonal_scalar_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    (nativeRationalCompactDiagonalScalar D L p χ).eval 1 =
      nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1) := by
  rw [nativeRationalCompactDiagonalScalar,scalar_unit_polynomial_eval,roughVectorMvProjection_eval,
    nativeIntegerLogPolynomialSequence,nativeLieLogarithmCharacter_exponential,Int.cast_one]

theorem native_rational_compact_univariate_coefficient_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (h N i : ℕ) (A : ℝ) (hi : 0 < i) (hiL : i ≤ ℓ)
    (hBounds : NativeRationalRelativeCoefficientBounds D L p hp h χ N A) :
    (N : ℝ)^i*‖((scalarDifferencePolynomial (nativeRationalCompactDiagonalScalar D L p χ)
      (nativeRationalCompactNonlinearScalar D L p hp χ) h (nativeRationalCompactCommutatorSlope D L p χ h)).coeff i :
        UnitAddCircle)‖ ≤ A := by
  rw [← native_rational_compact_univariate_difference D L p hp χ hχ h,scalar_unit_polynomial_coefficient]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Unit => i) = Finsupp.single () i := by
    apply Finsupp.ext
    intro j
    cases j
    simp
  have hb := hBounds.1 (fun _ => i) (by simpa using hi) (by simpa using hiL)
  simpa only [Finset.univ_unique,Finset.sum_singleton,he] using hb

end Hindman168
