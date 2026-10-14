import Hindman168.NativeCentralCharacterHorizontal

/-! An explicit fixed parent operator budget supplies the ACTUAL original
finite horizontal grid, not a character-size assumption on the pullback. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralCharacterBudget {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (A : ℝ) : ℝ := A * (1+‖nativeCenterQuotientProjection (I := D.I) (G := D.G)‖)

theorem native_central_character_budget_nonneg {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (A : ℝ) (hA : 0 ≤ A) : 0 ≤ nativeCentralCharacterBudget D A := by
  unfold nativeCentralCharacterBudget
  positivity

theorem native_central_character_budget_ge {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (A : ℝ) (hA : 0 ≤ A) : A ≤ nativeCentralCharacterBudget D A := by
  unfold nativeCentralCharacterBudget
  nlinarith only [norm_nonneg (nativeCenterQuotientProjection (I := D.I) (G := D.G)), hA]

theorem native_central_character_pullback_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (A : ℝ) (hA : 0 ≤ A) (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A) : ‖nativeCentralCharacterPullback D χ‖ ≤ nativeCentralCharacterBudget D A := by
  have hn := native_central_character_pullback_norm D χ
  have hm := mul_le_mul_of_nonneg_right hχ
    (norm_nonneg (nativeCenterQuotientProjection (I := D.I) (G := D.G)))
  unfold nativeCentralCharacterBudget
  nlinarith only [hn,hm,hA]

theorem native_central_character_pullback_grid {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (A : ℝ) (hA : 0 ≤ A) (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : ‖χ‖ ≤ A)
    (hHor : RoughNativeHorizontalFunctional (E := (nativeCentralQuotientData D).E)
      (I := (nativeCentralQuotientData D).I) (nativeCentralQuotientData D).Γ χ.toLinearMap) :
    (nativeCentralCharacterPullback D χ).toLinearMap ∈
      roughNativeHorizontalCharacterGrid (E := D.E) (I := D.I) D.Γ (nativeCentralCharacterBudget D A) :=
  rough_native_norm_bounded_horizontal_grid_mem D.Γ (nativeCentralCharacterBudget D A)
    (native_central_character_budget_nonneg D A hA) _
    (native_central_character_pullback_bound D A hA χ hχ)
    (native_central_character_pullback_horizontal D χ hHor)

end Hindman168
