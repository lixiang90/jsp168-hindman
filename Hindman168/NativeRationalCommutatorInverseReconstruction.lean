import Hindman168.NativeRationalCommutatorOriginalBounds
import Hindman168.NativeRationalCommutatorCharacterBudget

/-! FULL original inverse conclusion from a NONZERO actual commutator
candidate. Finite relative grid and bounded positive natural multiplier
give a genuine budget before ALL original source polynomials/lengths. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_commutator_inverse_reconstruction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (C : Finset ((nativeRationalRelativeData D L 1).E →L[ℝ] ℝ))
    (S : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (_hp : RoughVectorMvWeightedDegree L.layer p 0) (N : ℕ), 0 < N →
      ∀ χ ∈ C, ∀ hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
        (nativeRationalRelativeData D L 1).Γ χ.toLinearMap,
      ∀ M : ℕ, 0 < M → M ≤ S → ∀ i : NativeRationalFirstLayerIndex D L,
        (nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i).toLinearMap ≠ 0 →
        (N : ℝ)*‖(nativeRationalCompactBracketCoefficient D L p χ M i : UnitAddCircle)‖ ≤ B →
        ∃ f : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ f.toLinearMap ∧
          ‖f‖ ≤ (Q : ℝ) ∧ f.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
          (∀ J : Unit → ℕ, 0 < (∑ j, J j) → (N : ℝ)^(∑ j, J j)*
            ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
              (roughVectorMvProjection f.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
          ∀ J : Unit → ℕ, 0 < (∑ j, J j) → (N : ℝ)^(∑ j, J j)*
            ‖((mvPolynomialBinomialCoefficient (roughVectorMvProjection f.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  obtain ⟨R,hR,hbound⟩ := native_rational_integral_commutator_character_finite_budget D L C
  let d := nativeRationalFirstLayerDenominator D L*nativeRationalSplitBasisDenominator D L
  let E := (S : ℝ)*R+(d : ℝ)*B+(mvBinomialCoefficientBudget Unit ℓ : ℝ)*((d : ℝ)*B)+1
  let Q := ⌈E⌉₊+1
  have hSR : 0 ≤ (S : ℝ)*R := mul_nonneg (Nat.cast_nonneg S) hR
  have hdB : 0 ≤ (d : ℝ)*B := mul_nonneg (Nat.cast_nonneg d) hB
  have htB : 0 ≤ (mvBinomialCoefficientBudget Unit ℓ : ℝ)*((d : ℝ)*B) :=
    mul_nonneg (Nat.cast_nonneg _) hdB
  have hEQ : E ≤ (Q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ ⌈E⌉₊)
  have hNQ : (S : ℝ)*R ≤ (Q : ℝ) := (show _ ≤ E by dsimp only [E]; linarith).trans hEQ
  have hBQ : (d : ℝ)*B ≤ (Q : ℝ) := (show _ ≤ E by dsimp only [E]; linarith).trans hEQ
  have hTQ : (mvBinomialCoefficientBudget Unit ℓ : ℝ)*((d : ℝ)*B) ≤ (Q : ℝ) :=
    (show _ ≤ E by dsimp only [E]; linarith).trans hEQ
  refine ⟨Q,by dsimp only [Q]; omega,?_⟩
  intro p hp N hN χ hχC hHor M hM hMS i hne hsmall
  let f := (M : ℝ) • nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i
  obtain ⟨hOriginal,hMono,hBin⟩ := native_rational_integral_commutator_scaled_original_bounds
    D L χ hHor i hne p hp M N hM hN B hB hsmall
  have hNorm : ‖f‖ ≤ (Q : ℝ) := by
    change ‖(M : ℝ) • nativeRationalIntegralCommutatorCharacter D L χ hHor.2.1 i‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg M)]
    exact ((mul_le_mul_of_nonneg_left (hbound χ hχC hHor.2.1 i) (Nat.cast_nonneg M)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hMS) hR)).trans hNQ
  exact ⟨f,hOriginal,hNorm,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) f hNorm hOriginal,
    fun J hJ => (hMono J hJ).trans hBQ,fun J hJ => (hBin J hJ).trans hTQ⟩

end Hindman168
