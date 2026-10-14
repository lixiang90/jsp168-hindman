import Hindman168.NativeRationalRelativePolynomialSplitting
import Hindman168.NativeRationalRelativeCharacterBudget
import Hindman168.NativeRationalRelativeCoefficientScale

/-! Genuine ORIGINAL character and raw monomial bounds when the ACTUAL
relative difference character is zero. Nonzero difference and cancellation
cases remain open. No small-component conclusion is inferred from a sum. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_pure_diagonal_scalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hDiff : nativeRationalRelativeDifferenceCharacter D L χ = 0) :
    roughVectorMvProjection χ.toLinearMap (nativeRationalCompactRelativePolynomial D L p hp h) =
      roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
        (nativeRationalCompactNormalizedPolynomial D p) := by
  rw [native_rational_compact_relative_scalar_splitting]
  have hz : roughVectorMvProjection (nativeRationalRelativeDifferenceCharacter D L χ).toLinearMap
      (nativeRationalCompactDifferencePolynomial D L p hp h) = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [roughVectorMvProjection_eval,hDiff]
    simp
  rw [hz,add_zero]

theorem native_rational_pure_diagonal_original_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hDiff : nativeRationalRelativeDifferenceCharacter D L χ = 0)
    (J : Unit →₀ ℕ) (hJ : J ≠ 0) :
    ((MvPolynomial.coeff J (roughVectorMvProjection χ.toLinearMap
      (nativeRationalCompactRelativePolynomial D L p hp h)) : ℝ) : UnitAddCircle) =
    ((MvPolynomial.coeff J (roughVectorMvProjection
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p) : ℝ) : UnitAddCircle) := by
  have hχ : χ ≠ 0 := by
    intro hz
    exact hHor.1 (congrArg ContinuousLinearMap.toLinearMap hz)
  have hDiag := (native_rational_relative_character_nonzero_alternative D L χ hχ).resolve_right
    (not_not_intro hDiff)
  have hOriginal := native_rational_relative_diagonal_character_horizontal D L χ hHor hDiag
  obtain ⟨z,hz⟩ := native_two_normalizations_original_nonconstant_coefficients D p
    (nativeRationalBasepointRepresentative D p) (nativeRationalLinearLatticePart D p)
    (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap hOriginal.2.1
    (fun γ => hOriginal.2.2 γ γ.property) J hJ
  rw [native_rational_pure_diagonal_scalar D L p hp h χ hDiff]
  change (((MvPolynomial.coeff J (roughVectorMvProjection
    (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
      (nativeRationalCompactNormalizedPolynomial D p))) : ℝ) : UnitAddCircle) = _
  rw [nativeRationalCompactNormalizedPolynomial,hz,AddCircle.coe_add]
  have hz0 : ((z : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z,by simp only [zsmul_eq_mul,mul_one]⟩
  rw [hz0,add_zero]

theorem native_rational_pure_diagonal_original_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hDiff : nativeRationalRelativeDifferenceCharacter D L χ = 0) (N : ℕ) (B : ℝ)
    (hCoeff : NativeRationalRelativeCoefficientBounds D L p hp h χ N B)
    (J : Unit → ℕ) (hJ : 0 < (∑ i, J i)) (hdeg : (∑ i, J i) ≤ ℓ) :
    (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
      (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p) : ℝ) :
        UnitAddCircle)‖ ≤ B := by
  have hne : Finsupp.equivFunOnFinite.symm J ≠ 0 := by
    intro hz
    have he : J = 0 := by
      funext i
      have ht := congrArg (fun q : Unit →₀ ℕ => q i) hz
      change J i = 0 at ht
      exact ht
    rw [he] at hJ
    simp at hJ
  rw [← native_rational_pure_diagonal_original_coefficient D L p hp h χ hHor hDiff _ hne]
  exact hCoeff.1 J hJ hdeg

end Hindman168
