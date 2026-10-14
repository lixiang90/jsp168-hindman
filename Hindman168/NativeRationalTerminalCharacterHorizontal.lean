import Hindman168.NativeRationalTerminalCharacterPullback
import Hindman168.NativeContinuousHorizontalCharacter

/-! ORIGINAL horizontal commutator annihilation and ORIGINAL lattice
integrality are PROVED for the actual terminal character pullback. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_terminal_character_pullback_mul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalTerminalQuotientData D L).I)
      (G := (nativeRationalTerminalQuotientData D L).G) 1 ≤ χ.toLinearMap.ker) (g h : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalTerminalCharacterPullback D L χ).toLinearMap (g*h) =
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalTerminalCharacterPullback D L χ).toLinearMap g +
      nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalTerminalCharacterPullback D L χ).toLinearMap h := by
  rw [native_rational_terminal_character_pullback_log,native_rational_terminal_character_pullback_log,
    native_rational_terminal_character_pullback_log,map_mul]
  exact nativeLieLogarithmCharacter_mul (I := (nativeRationalTerminalQuotientData D L).I)
    (G := (nativeRationalTerminalQuotientData D L).G) χ.toLinearMap hχ _ _

theorem native_rational_terminal_character_pullback_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalTerminalQuotientData D L).I)
      (G := (nativeRationalTerminalQuotientData D L).G) 1 ≤ χ.toLinearMap.ker) :
    nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ (nativeRationalTerminalCharacterPullback D L χ).toLinearMap.ker :=
  native_continuous_character_linearization_horizontal (I := D.I)
    (nativeLieLogarithmCharacter (I := D.I) (G := D.G) (nativeRationalTerminalCharacterPullback D L χ).toLinearMap)
    (native_rational_terminal_character_pullback_mul D L χ hχ) (nativeRationalTerminalCharacterPullback D L χ)
    (fun _ => rfl)

theorem native_rational_terminal_character_pullback_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ)
    (hχ : ∀ γ ∈ (nativeRationalTerminalQuotientData D L).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeRationalTerminalQuotientData D L).E)
        (I := (nativeRationalTerminalQuotientData D L).I) (G := (nativeRationalTerminalQuotientData D L).G) γ) = (m : ℝ)) :
    ∀ γ ∈ D.Γ, ∃ m : ℤ, nativeRationalTerminalCharacterPullback D L χ
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) = (m : ℝ) := by
  intro γ hγ
  have hm : nativeRationalTerminalGroupProjection D L γ ∈ (nativeRationalTerminalQuotientData D L).Γ :=
    Subgroup.mem_map.mpr ⟨γ,hγ,rfl⟩
  obtain ⟨m,he⟩ := hχ _ hm
  rw [native_rational_terminal_data_logarithm] at he
  exact ⟨m,he⟩

theorem native_rational_terminal_character_pullback_horizontal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalTerminalQuotientData D L).E →L[ℝ] ℝ)
    (hχ : RoughNativeHorizontalFunctional (I := (nativeRationalTerminalQuotientData D L).I)
      (nativeRationalTerminalQuotientData D L).Γ χ.toLinearMap) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ (nativeRationalTerminalCharacterPullback D L χ).toLinearMap := by
  refine ⟨?_,native_rational_terminal_character_pullback_commutator D L χ hχ.2.1,
    native_rational_terminal_character_pullback_lattice D L χ hχ.2.2⟩
  intro hz
  apply hχ.1
  ext v
  obtain ⟨u,rfl⟩ := native_rational_terminal_model_projection_surjective D L v
  have he := DFunLike.congr_fun hz u
  simpa only [ContinuousLinearMap.coe_coe,native_rational_terminal_character_pullback_apply,LinearMap.zero_apply] using he

end Hindman168
