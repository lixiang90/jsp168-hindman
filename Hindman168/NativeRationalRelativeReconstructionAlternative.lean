import Hindman168.NativeRationalRelativeCharacterBudget
import Hindman168.NativeRationalRelativeDifferenceCharacter

/-! Genuine bounded reconstruction alternative: ORIGINAL horizontal diagonal
character, or a nonzero character of the actual F_2 subgroup when diagonal is zero.
The latter is not declared an original horizontal character. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_relative_reconstruction_alternative {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalRelativeData D L 1).I)
      (nativeRationalRelativeData D L 1).Γ χ.toLinearMap) :
    (RoughNativeHorizontalFunctional (I := D.I) D.Γ
        (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap ∧
      ‖nativeRationalRelativeDiagonalCharacter D L χ‖ ≤ nativeRationalRelativeCharacterBudget D L A ∧
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap ∈
        roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (nativeRationalRelativeCharacterBudget D L A)) ∨
    (nativeRationalRelativeDiagonalCharacter D L χ = 0 ∧
      nativeRationalRelativeDifferenceCharacter D L χ ≠ 0 ∧
      ‖nativeRationalRelativeDifferenceCharacter D L χ‖ ≤ nativeRationalRelativeCharacterBudget D L A ∧
      nativeRationalRelativeDifferenceLogCharacter D L χ ≠ 0) := by
  classical
  by_cases hDiag : nativeRationalRelativeDiagonalCharacter D L χ ≠ 0
  · exact Or.inl ⟨native_rational_relative_diagonal_character_horizontal D L χ hHor hDiag,
      native_rational_relative_diagonal_character_bound D L A hA χ hχ,
      native_rational_relative_diagonal_character_grid D L A hA χ hχ hHor hDiag⟩
  · have hZero : nativeRationalRelativeDiagonalCharacter D L χ = 0 := not_not.mp hDiag
    have hNonzero : χ ≠ 0 := by
      intro hz
      apply hHor.1
      exact congrArg ContinuousLinearMap.toLinearMap hz
    have hDiff := (native_rational_relative_character_nonzero_alternative D L χ hNonzero).resolve_left hDiag
    exact Or.inr ⟨hZero,hDiff,native_rational_relative_difference_character_bound D L A hA χ hχ,
      native_rational_relative_difference_log_character_nonzero D L χ hDiff⟩

end Hindman168
