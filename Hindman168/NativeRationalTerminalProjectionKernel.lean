import Hindman168.NativeRationalTerminalProjection

/-! The ACTUAL terminal model projection is surjective and has precisely
the ORIGINAL terminal layer as kernel. -/

namespace Hindman168
universe u

theorem native_rational_terminal_model_projection_surjective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    Function.Surjective (nativeRationalTerminalModelProjection D F) := by
  change Function.Surjective (F.layer ℓ).mkQ
  exact (F.layer ℓ).mkQ_surjective

theorem native_rational_terminal_model_projection_kernel {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeRationalTerminalModelProjection D F).toLinearMap.ker = F.layer ℓ := by
  exact Submodule.ker_mkQ (F.layer ℓ)

theorem native_rational_terminal_model_projection_zero_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (v : D.E) :
    nativeRationalTerminalModelProjection D F v = 0 ↔ v ∈ F.layer ℓ := by
  rw [← native_rational_terminal_model_projection_kernel D F]
  rfl

end Hindman168
