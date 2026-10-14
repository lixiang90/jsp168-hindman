import Hindman168.NativeRationalTerminalProjection
import Hindman168.LieExponentialHomomorphism

/-! Actual original native terminal quotient projection, identity differential and Exp/Log/rational span transport. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_data_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (v : D.E) :
    nativeRationalTerminalGroupProjection D F
      (nativeLieExponential (E := D.E)
        (I := D.I) (G := D.G) v) =
      nativeLieExponential (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)
        (nativeRationalTerminalModelProjection D F v) := by
  have h := nativeLieExponential_map (I := D.I)
    (J := (nativeRationalTerminalQuotientData D F).I) (nativeRationalTerminalGroupProjection D F)
    ((native_rational_terminal_projection_contMDiff D F).mdifferentiable (by norm_num)) v
  rw [native_rational_terminal_projection_mfderiv] at h
  exact h

theorem native_rational_terminal_data_logarithm {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (g : D.G) :
    nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
      (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)
      (nativeRationalTerminalGroupProjection D F g) =
    nativeRationalTerminalModelProjection D F
      (nativeLieGlobalLogarithm (E := D.E)
        (I := D.I) (G := D.G) g) := by
  have h := native_rational_terminal_data_exponential D F
    (nativeLieGlobalLogarithm (E := D.E)
      (I := D.I) (G := D.G) g)
  rw [nativeLieExponential_globalLogarithm] at h
  have hl := congrArg (nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
    (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) h
  rw [nativeLieGlobalLogarithm_exponential] at hl
  exact hl

end Hindman168
