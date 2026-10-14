import Hindman168.NativeRationalTerminalCharacterHorizontal

/-! A FIXED ORIGINAL true operator budget supplies the ORIGINAL finite
horizontal-character grid for the actual nonzero quotient pullback. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalTerminalCharacterBudget {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) : ℝ :=
  A * (1+‖nativeRationalTerminalModelProjection D L‖)

theorem native_rational_terminal_character_budget_nonneg {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ nativeRationalTerminalCharacterBudget D L A := by unfold nativeRationalTerminalCharacterBudget; positivity

theorem native_rational_terminal_character_budget_ge {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A) :
    A ≤ nativeRationalTerminalCharacterBudget D L A := by
  unfold nativeRationalTerminalCharacterBudget
  nlinarith only [norm_nonneg (nativeRationalTerminalModelProjection D L),hA]

theorem native_rational_terminal_character_pullback_bound {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A) :
    ‖nativeRationalTerminalCharacterPullback D L χ‖ ≤ nativeRationalTerminalCharacterBudget D L A := by
  have hn := native_rational_terminal_character_pullback_norm D L χ
  have hm := mul_le_mul_of_nonneg_right hχ (norm_nonneg (nativeRationalTerminalModelProjection D L))
  unfold nativeRationalTerminalCharacterBudget
  nlinarith only [hn,hm,hA]

theorem native_rational_terminal_character_pullback_grid {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (A : ℝ) (hA : 0 ≤ A)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (hχ : ‖χ‖ ≤ A)
    (hHor : RoughNativeHorizontalFunctional (I := (nativeRationalTerminalQuotientData D L).I)
      (nativeRationalTerminalQuotientData D L).Γ χ.toLinearMap) :
    (nativeRationalTerminalCharacterPullback D L χ).toLinearMap ∈
      roughNativeHorizontalCharacterGrid (I := D.I) D.Γ (nativeRationalTerminalCharacterBudget D L A) :=
  rough_native_norm_bounded_horizontal_grid_mem D.Γ (nativeRationalTerminalCharacterBudget D L A)
    (native_rational_terminal_character_budget_nonneg D L A hA) _
    (native_rational_terminal_character_pullback_bound D L A hA χ hχ)
    (native_rational_terminal_character_pullback_horizontal D L χ hHor)

end Hindman168
