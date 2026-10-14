import Hindman168.NativeRationalPureDiagonalReconstruction
import Hindman168.RoughVectorZeroTrimProjection
import Hindman168.MvBinomialCoefficientModOne

/-! The TRUE zero difference-character case gives a COMPLETE original
inverse from one actual useful shift. Both tables include ALL positive
multiindices; high-degree zero vector terms are handled by exact trimming. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_pure_diagonal_complete_monomial_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h : ℤ) (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hDiff : nativeRationalRelativeDifferenceCharacter D L χ = 0) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hCoeff : NativeRationalRelativeCoefficientBounds D L p hp h χ N B) :
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
        (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ B := by
  intro J hJ
  by_cases hdeg : (∑ i, J i) ≤ ℓ
  · exact native_rational_pure_diagonal_original_bound D L p hp h χ hHor hDiff N B hCoeff J hJ hdeg
  · have hd : (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p).totalDegree ≤ ℓ := by
      rw [← rough_vector_zero_trim_projection]
      exact roughVectorMvProjection_degree _ (rough_vector_zero_trim_degree L.layer L.antitone hp L.terminal)
    rw [scalar_mv_coefficient_zero_above_degree _ ℓ hd J (Nat.lt_of_not_ge hdeg),
      AddCircle.coe_zero,norm_zero,mul_zero]
    exact hB

theorem native_rational_pure_diagonal_inverse_reconstruction {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (hp : RoughVectorMvWeightedDegree L.layer p 0) (h : ℤ)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
        (nativeRationalRelativeData D L 1).Γ χ.toLinearMap → ‖χ‖ ≤ A →
      nativeRationalRelativeDifferenceCharacter D L χ = 0 → ∀ N : ℕ, 0 < N →
      NativeRationalRelativeCoefficientBounds D L p hp h χ N B →
      ∃ f : D.E →L[ℝ] ℝ, RoughNativeHorizontalFunctional (I := D.I) D.Γ f.toLinearMap ∧
        ‖f‖ ≤ (Q : ℝ) ∧ f.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (Q : ℝ) ∧
        (∀ J : Unit → ℕ, 0 < (∑ i, J i) → (N : ℝ)^(∑ i, J i)*
          ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
            (roughVectorMvProjection f.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)) ∧
        ∀ J : Unit → ℕ, 0 < (∑ i, J i) → (N : ℝ)^(∑ i, J i)*
          ‖((mvPolynomialBinomialCoefficient (roughVectorMvProjection f.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ) := by
  let R := nativeRationalRelativeCharacterBudget D L A
  let E := R+B+(mvBinomialCoefficientBudget Unit ℓ : ℝ)*B+1
  let Q := ⌈E⌉₊+1
  have hR : 0 ≤ R := hA.trans (native_rational_relative_character_budget_ge D L A hA)
  have htB : 0 ≤ (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B := mul_nonneg (Nat.cast_nonneg _) hB
  have hEQ : E ≤ (Q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ ⌈E⌉₊)
  have hRQ : R ≤ (Q : ℝ) := (show R ≤ E by dsimp only [E]; linarith).trans hEQ
  have hBQ : B ≤ (Q : ℝ) := (show B ≤ E by dsimp only [E]; linarith).trans hEQ
  have hTQ : (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B ≤ (Q : ℝ) :=
    (show _ ≤ E by dsimp only [E]; linarith).trans hEQ
  refine ⟨Q,by dsimp only [Q]; omega,?_⟩
  intro p hp h χ hHor hNorm hDiff N hN hCoeff
  have hχ : χ ≠ 0 := by
    intro hz
    exact hHor.1 (congrArg ContinuousLinearMap.toLinearMap hz)
  have hDiag := (native_rational_relative_character_nonzero_alternative D L χ hχ).resolve_right (not_not_intro hDiff)
  let f := nativeRationalRelativeDiagonalCharacter D L χ
  have hOriginal := native_rational_relative_diagonal_character_horizontal D L χ hHor hDiag
  have hNormQ := (native_rational_relative_diagonal_character_bound D L A hA χ hNorm).trans hRQ
  have hMono := native_rational_pure_diagonal_complete_monomial_bounds D L p hp h χ hHor hDiff N B hB hCoeff
  refine ⟨f,hOriginal,hNormQ,
    rough_native_norm_bounded_horizontal_grid_mem D.Γ _ (Nat.cast_nonneg Q) f hNormQ hOriginal,
    fun J hJ => (hMono J hJ).trans hBQ,?_⟩
  intro J hJ
  by_cases hdeg : (∑ i, J i) ≤ ℓ
  · have hb := mv_binomial_coefficient_mod_one (roughVectorMvProjection f.toLinearMap p)
      ℓ 1 1 J (mv_binomial_box_mem_of_weight_le ℓ J hdeg) hJ (N : ℝ) B
      (by exact_mod_cast hN) hB (fun I _ hI => by simpa only [Nat.cast_one,one_mul] using hMono I hI)
    simpa only [Nat.cast_one,one_mul] using hb.trans hTQ
  · have hd : (roughVectorMvProjection f.toLinearMap p).totalDegree ≤ ℓ := by
      rw [← rough_vector_zero_trim_projection]
      exact roughVectorMvProjection_degree _ (rough_vector_zero_trim_degree L.layer L.antitone hp L.terminal)
    rw [mv_binomial_coefficient_zero_above_degree _ ℓ hd J (Nat.lt_of_not_ge hdeg),AddCircle.coe_zero,norm_zero,mul_zero]
    exact Nat.cast_nonneg Q

end Hindman168
