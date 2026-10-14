import Hindman168.NativeRationalCompactScalarDifferencePolynomial
import Hindman168.NativeRationalRelativeCoefficientScale
import Hindman168.ScalarUnitPolynomial
import Hindman168.ScalarDifferenceSecondCoefficient

/-! Exact actual compact P/Q/sigma in ordinary univariate coefficients,
with true degree and direct transfer of the actual second coefficient bound. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff BigOperators
universe u

noncomputable def nativeRationalCompactDiagonalScalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : ℝ[X] :=
  scalarUnitPolynomial (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
    (nativeRationalCompactNormalizedPolynomial D p))

noncomputable def nativeRationalCompactNonlinearScalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : ℝ[X] :=
  scalarUnitPolynomial (nativeRationalNonlinearScalar D L (nativeRationalCompactNormalizedPolynomial D p)
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) χ)

noncomputable def nativeRationalCompactCommutatorSlope {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (h : ℕ) : ℝ :=
  nativeRationalRelativeCommutatorValue D L χ
    (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)
    (nativeRationalShiftRepresentative D p h)

theorem native_rational_compact_nonlinear_scalar_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) :
    (nativeRationalCompactNonlinearScalar D L p hp χ).natDegree ≤ ℓ :=
  scalar_unit_polynomial_degree _ ℓ (native_rational_nonlinear_scalar_degree D L
    (nativeRationalCompactNormalizedPolynomial D p)
    (native_rational_compact_normalized_polynomial_weighted D L hp)
    (native_rational_compact_normalized_polynomial_zero D p) χ)

theorem native_rational_compact_univariate_difference {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker) (h : ℕ) :
    scalarUnitPolynomial (roughVectorMvProjection χ.toLinearMap
      (nativeRationalCompactRelativePolynomial D L p hp h)) =
    scalarDifferencePolynomial (nativeRationalCompactDiagonalScalar D L p χ)
      (nativeRationalCompactNonlinearScalar D L p hp χ) h (nativeRationalCompactCommutatorSlope D L p χ h) := by
  have he := congrArg (MvPolynomial.uniqueAlgEquiv ℝ Unit)
    (native_rational_compact_scalar_difference_polynomial D L p hp χ hχ h)
  dsimp only [scalarDifferencePolynomial,nativeRationalCompactDiagonalScalar,
    nativeRationalCompactNonlinearScalar,nativeRationalCompactCommutatorSlope]
  simp only [map_add,map_sub,map_mul] at he
  change scalarUnitPolynomial _ = scalarUnitPolynomial _+scalarUnitPolynomial _-scalarUnitPolynomial _+
    scalarUnitPolynomial (MvPolynomial.C _)*scalarUnitPolynomial (MvPolynomial.X ()) at he
  rw [scalar_unit_polynomial_translation,scalar_unit_polynomial_C,scalar_unit_polynomial_X] at he
  simpa only [Int.cast_natCast] using he

theorem native_rational_compact_univariate_second_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (h N : ℕ) (A : ℝ) (hBounds : NativeRationalRelativeCoefficientBounds D L p hp h χ N A) :
    (N : ℝ)^2*‖((scalarDifferencePolynomial (nativeRationalCompactDiagonalScalar D L p χ)
      (nativeRationalCompactNonlinearScalar D L p hp χ) h (nativeRationalCompactCommutatorSlope D L p χ h)).coeff 2 :
        UnitAddCircle)‖ ≤ A := by
  rw [← native_rational_compact_univariate_difference D L p hp χ hχ h,scalar_unit_polynomial_coefficient]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Unit => 2) = Finsupp.single () 2 := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  have hb := hBounds.1 (fun _ => 2) (by simp) (by simpa using hdeg)
  simpa only [Finset.univ_unique,Finset.sum_singleton,he] using hb

end Hindman168
