import Hindman168.NativeRationalRelativeCharacterSplitting
import Hindman168.NativeRationalTerminalCharacterGrid

/-! Fixed actual diagonal/difference operator budgets and genuine ORIGINAL
horizontal grid when the actual diagonal component is nonzero. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalRelativeCharacterBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) : ℝ :=
  A * (1+‖nativeRationalRelativeDiagonalModel D L‖+‖nativeRationalRelativeFirstDifferenceModel D L‖)

theorem native_rational_relative_character_budget_ge {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A) :
    A ≤ nativeRationalRelativeCharacterBudget D L A := by
  unfold nativeRationalRelativeCharacterBudget
  nlinarith only [hA,norm_nonneg (nativeRationalRelativeDiagonalModel D L),
    norm_nonneg (nativeRationalRelativeFirstDifferenceModel D L)]

theorem native_rational_relative_diagonal_character_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A) :
    ‖nativeRationalRelativeDiagonalCharacter D L χ‖ ≤ nativeRationalRelativeCharacterBudget D L A := by
  have hn := χ.opNorm_comp_le (nativeRationalRelativeDiagonalModel D L)
  have hm := mul_le_mul_of_nonneg_right hχ (norm_nonneg (nativeRationalRelativeDiagonalModel D L))
  change ‖nativeRationalRelativeDiagonalCharacter D L χ‖ ≤ ‖χ‖*‖nativeRationalRelativeDiagonalModel D L‖ at hn
  unfold nativeRationalRelativeCharacterBudget
  nlinarith only [hn,hm,hA,norm_nonneg (nativeRationalRelativeFirstDifferenceModel D L)]

theorem native_rational_relative_difference_character_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A) :
    ‖nativeRationalRelativeDifferenceCharacter D L χ‖ ≤ nativeRationalRelativeCharacterBudget D L A := by
  have hn := χ.opNorm_comp_le (nativeRationalRelativeFirstDifferenceModel D L)
  have hm := mul_le_mul_of_nonneg_right hχ (norm_nonneg (nativeRationalRelativeFirstDifferenceModel D L))
  change ‖nativeRationalRelativeDifferenceCharacter D L χ‖ ≤ ‖χ‖*‖nativeRationalRelativeFirstDifferenceModel D L‖ at hn
  unfold nativeRationalRelativeCharacterBudget
  nlinarith only [hn,hm,hA,norm_nonneg (nativeRationalRelativeDiagonalModel D L)]

theorem native_rational_relative_diagonal_character_grid {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap)
    (hne : nativeRationalRelativeDiagonalCharacter D L χ ≠ 0) :
    (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap ∈
      roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (nativeRationalRelativeCharacterBudget D L A) :=
  rough_native_norm_bounded_horizontal_grid_mem D.Γ _
    (hA.trans (native_rational_relative_character_budget_ge D L A hA)) _
    (native_rational_relative_diagonal_character_bound D L A hA χ hχ)
    (native_rational_relative_diagonal_character_horizontal D L χ hHor hne)

end Hindman168
