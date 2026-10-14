import Hindman168.NativeRationalIntegralCommutatorCharacter
import Hindman168.NativeRationalKillsTwoOriginalBounds
import Hindman168.NativeFilteredHorizontalMultiplier
import Hindman168.ModOneNaturalMultiplier

/-! Actual commutator small coefficient yields BOTH COMPLETE ORIGINAL
tables for the positive natural multiple of the TRUE integral character. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_integral_commutator_scaled_compact_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (p : RoughVectorMvPolynomial Unit D.E) (M : ℕ) (i : NativeRationalFirstLayerIndex D L) :
    ((M : ℝ) • nativeRationalIntegralCommutatorCharacter D L χ hχ i)
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) =
      ((nativeRationalFirstLayerDenominator D L*nativeRationalSplitBasisDenominator D L : ℕ) : ℝ)*
        nativeRationalCompactBracketCoefficient D L p χ M i := by
  have hq : (nativeRationalFirstLayerDenominator D L : ℝ) ≠ 0 := by
    exact_mod_cast (native_rational_first_layer_denominator_positive D L).ne'
  change (M : ℝ)*nativeRationalIntegralCommutatorCharacter D L χ hχ i _ = _
  rw [native_rational_integral_commutator_character_evaluation]
  dsimp only [nativeRationalCompactBracketCoefficient,nativeRationalCommutatorFirstLayerCoefficient]
  push_cast
  field_simp

theorem native_rational_integral_commutator_scaled_original_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (i : NativeRationalFirstLayerIndex D L)
    (hne : (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap ≠ 0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : (N : ℝ)*‖(nativeRationalCompactBracketCoefficient D L p χ M i : UnitAddCircle)‖ ≤ B) :
    let f := (M : ℝ) • nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i
    RoughNativeHorizontalFunctional (I := D.I) D.Γ f.toLinearMap ∧
      (∀ J : Unit → ℕ, 0 < (∑ j, J j) → (N : ℝ)^(∑ j, J j)*
        ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
          (roughVectorMvProjection f.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤
            ((nativeRationalFirstLayerDenominator D L*nativeRationalSplitBasisDenominator D L : ℕ) : ℝ)*B) ∧
      ∀ J : Unit → ℕ, 0 < (∑ j, J j) → (N : ℝ)^(∑ j, J j)*
        ‖((mvPolynomialBinomialCoefficient (roughVectorMvProjection f.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤
          (mvBinomialCoefficientBudget Unit ℓ : ℝ)*
            (((nativeRationalFirstLayerDenominator D L*nativeRationalSplitBasisDenominator D L : ℕ) : ℝ)*B) := by
  let f := (M : ℝ) • nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i
  have hOriginal : RoughNativeHorizontalFunctional (I := D.I) D.Γ f.toLinearMap :=
    native_filtered_horizontal_natural_multiple (I := D.I) D.Γ _
      (native_rational_integral_commutator_character_horizontal D L χ hHor i hne) M hM
  have hf2 : L.layer 2 ≤ f.toLinearMap.ker := by
    intro v hv
    have hz := native_rational_integral_commutator_character_kills_two D L χ hHor.2.1 i hv
    change nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i v = 0 at hz
    change (M : ℝ)*nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i v = 0
    exact (congrArg (fun t : ℝ => (M : ℝ)*t) hz).trans (mul_zero _)
  let d := nativeRationalFirstLayerDenominator D L*nativeRationalSplitBasisDenominator D L
  have hsmall' : (N : ℝ)*‖((f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) : ℝ) : UnitAddCircle)‖ ≤
        (d : ℝ)*B := by
    rw [native_rational_integral_commutator_scaled_compact_evaluation]
    have hh := mul_le_mul_of_nonneg_left (mod_one_natural_multiplier_norm_le d
      (nativeRationalCompactBracketCoefficient D L p χ M i)) (Nat.cast_nonneg N)
    have hb := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg d)
    nlinarith
  refine ⟨hOriginal,?_,?_⟩
  · exact native_rational_kills_two_original_monomial_bounds D L p hp f hf2 hOriginal.2.2 N
      ((d : ℝ)*B) (mul_nonneg (Nat.cast_nonneg d) hB) hsmall'
  · exact native_rational_kills_two_original_binomial_bounds D L p hp f hf2 hOriginal.2.2 N hN
      ((d : ℝ)*B) (mul_nonneg (Nat.cast_nonneg d) hB) hsmall'

end Hindman168
