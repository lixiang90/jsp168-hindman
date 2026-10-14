import Hindman168.NativeRationalTerminalProjectionKernel
import Hindman168.NativeRationalTerminalExponentialLogarithm
import Hindman168.NativeLieLogarithmCharacter

/-! Actual terminal native characters pull back through the TRUE ORIGINAL
model/group projection. Nonzero follows from PROVED original surjectivity. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalTerminalCharacterPullback {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) : D.E →L[ℝ] ℝ :=
  χ.comp (nativeRationalTerminalModelProjection D L)

theorem native_rational_terminal_character_pullback_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (v : D.E) :
    nativeRationalTerminalCharacterPullback D L χ v = χ (nativeRationalTerminalModelProjection D L v) := rfl

theorem native_rational_terminal_character_pullback_norm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) :
    ‖nativeRationalTerminalCharacterPullback D L χ‖ ≤ ‖χ‖ * ‖nativeRationalTerminalModelProjection D L‖ :=
  χ.opNorm_comp_le _

theorem native_rational_terminal_character_pullback_nonzero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (hχ : χ ≠ 0) :
    nativeRationalTerminalCharacterPullback D L χ ≠ 0 := by
  intro hz
  apply hχ
  ext v
  obtain ⟨u,rfl⟩ := native_rational_terminal_model_projection_surjective D L v
  have he := congrArg (fun f : D.E →L[ℝ] ℝ => f u) hz
  simpa only [native_rational_terminal_character_pullback_apply,zero_apply] using he

theorem native_rational_terminal_character_pullback_log {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ) (g : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalTerminalCharacterPullback D L χ).toLinearMap g =
      nativeLieLogarithmCharacter (I := (nativeRationalTerminalQuotientData D L).I)
        (G := (nativeRationalTerminalQuotientData D L).G) χ.toLinearMap (nativeRationalTerminalGroupProjection D L g) := by
  change χ (nativeRationalTerminalModelProjection D L
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)) = _
  rw [← native_rational_terminal_data_logarithm]
  rfl

end Hindman168
