import Hindman168.NativeRationalTerminalImageLayers

/-! The new native filtration's integrated group layers are EXACT original
terminal projection image layers; the actual group filtration loses a degree. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_image_group_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    nativeRationalFilteredGroupLayer (nativeRationalTerminalQuotientData D F)
      (nativeTerminalRationalLieFiltration D F) i = nativeRationalTerminalImageGroupLayer D F i := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff,native_rational_terminal_image_logarithm_iff]
  rfl

theorem native_rational_terminal_image_group_conditions {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    CubeGroupFiltration (nativeRationalTerminalImageGroupLayer D F) :=
  (native_rational_filtered_group_conditions D F).map (nativeRationalTerminalGroupProjection D F)

theorem native_rational_terminal_image_group_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalImageGroupLayer D F 0 = ⊤ := by
  rw [← native_rational_terminal_image_group_eq]
  exact native_rational_filtered_group_zero _ _

theorem native_rational_terminal_image_group_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalImageGroupLayer D F 1 = ⊤ := by
  rw [← native_rational_terminal_image_group_eq]
  exact native_rational_filtered_group_one _ _

theorem native_rational_terminal_image_group_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (hi : ℓ ≤ i) :
    nativeRationalTerminalImageGroupLayer D F i = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have hm := (native_rational_terminal_image_logarithm_iff D F i g).mp hg
  rw [native_rational_terminal_image_lie_terminal D F i hi,Submodule.mem_bot] at hm
  change g = 1
  exact (nativeLieExponential_globalLogarithm (E := (nativeRationalTerminalQuotientData D F).E)
    (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G) g).symm.trans
      ((congrArg (nativeLieExponential (E := (nativeRationalTerminalQuotientData D F).E)
        (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)) hm).trans
          (nativeLieExponential_zero (E := (nativeRationalTerminalQuotientData D F).E)
            (I := (nativeRationalTerminalQuotientData D F).I) (G := (nativeRationalTerminalQuotientData D F).G)))

end Hindman168
