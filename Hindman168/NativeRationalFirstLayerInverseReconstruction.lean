import Hindman168.NativeRationalFirstLayerOriginalBounds

/-! FULL original univariate inverse conclusion from an actual bounded
nonzero first-layer integer vector with small k dot gamma. All reconstruction,
raw normalization, norm, original grid and BOTH COMPLETE tables are proved. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_first_layer_inverse_reconstruction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E),
      RoughVectorMvWeightedDegree L.layer p 0 → ∀ N : ℕ, 0 < N →
        ∀ k : NativeRationalFirstLayerIndex D L → ℤ, k ≠ 0 →
          (∀ i, |(k i : ℝ)| ≤ R) →
          (N : ℝ)*‖((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ B →
          ∃ χ : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap ∧
            ‖χ‖ ≤ (Q : ℝ) ∧ χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
            (∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
                (roughVectorMvProjection χ.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
            ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
              (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
                (roughVectorMvProjection χ.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  let A := R*(∑ i : NativeRationalFirstLayerIndex D L,
    ‖(nativeRationalFirstLayerCoordinate D L i).toContinuousLinearMap‖)
  let C := A+B+(mvBinomialCoefficientBudget Unit ℓ : ℝ)*B+1
  let Q := ⌈C⌉₊+1
  have hA : 0 ≤ A := mul_nonneg hR (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hBB : 0 ≤ (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B := mul_nonneg (Nat.cast_nonneg _) hB
  have hCQ : C ≤ (Q : ℝ) := (Nat.le_ceil C).trans (by exact_mod_cast (Nat.le_succ ⌈C⌉₊))
  have hAQ : A ≤ (Q : ℝ) := (show A ≤ C by dsimp only [C]; linarith).trans hCQ
  have hBQ : B ≤ (Q : ℝ) := (show B ≤ C by dsimp only [C]; linarith).trans hCQ
  have hBBQ : (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B ≤ (Q : ℝ) :=
    (show _ ≤ C by dsimp only [C]; linarith).trans hCQ
  refine ⟨Q,by dsimp only [Q]; omega,?_⟩
  intro p hp N hN k hk hki hsmall
  let χ := nativeRationalFirstLayerIntegerCharacter D L k
  have hhor := native_rational_first_layer_integer_character_horizontal D L k hk
  have hnorm : ‖χ‖ ≤ (Q : ℝ) :=
    (native_rational_first_layer_integer_character_norm D L k R hki).trans hAQ
  refine ⟨χ,hhor,hnorm,rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) χ hnorm hhor,?_,?_⟩
  · intro J hJ
    exact (native_rational_first_layer_original_monomial_bounds D L p hp k N B hB hsmall J hJ).trans hBQ
  · intro J hJ
    exact (native_rational_first_layer_original_binomial_bounds D L p hp k N hN B hB hsmall J hJ).trans hBBQ

end Hindman168
