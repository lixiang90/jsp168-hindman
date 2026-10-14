import Hindman168.NativeCentralQuotientProjection
import Hindman168.NativeLieLogarithmCharacter

/-! Actual child functional pulled back through the ORIGINAL center-model
projection. Its nonzero property follows from the genuine right section. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralCharacterPullback {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) : D.E →L[ℝ] ℝ :=
  χ.comp (nativeCenterQuotientProjection (I := D.I) (G := D.G))

theorem native_central_character_pullback_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) (v : D.E) :
    nativeCentralCharacterPullback D χ v =
      χ (nativeCenterQuotientProjection (I := D.I) (G := D.G) v) := rfl

theorem native_central_character_pullback_norm {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) :
    ‖nativeCentralCharacterPullback D χ‖ ≤
      ‖χ‖ * ‖nativeCenterQuotientProjection (I := D.I) (G := D.G)‖ :=
  χ.opNorm_comp_le _

theorem native_central_character_pullback_nonzero {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) (hχ : χ ≠ 0) :
    nativeCentralCharacterPullback D χ ≠ 0 := by
  intro hz
  apply hχ
  ext v
  have h := congrArg (fun f : D.E →L[ℝ] ℝ =>
    f (nativeCenterQuotientSection (I := D.I) (G := D.G) v)) hz
  simpa only [native_central_character_pullback_apply, nativeCenterQuotientSection_right,
    zero_apply] using h

theorem native_central_character_pullback_log {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ) (g : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeCentralCharacterPullback D χ).toLinearMap g =
      nativeLieLogarithmCharacter (I := (nativeCentralQuotientData D).I)
        (G := (nativeCentralQuotientData D).G) χ.toLinearMap
          (g : D.G ⧸ Subgroup.center D.G) := by
  change χ (nativeCenterQuotientProjection (I := D.I) (G := D.G)
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)) = _
  rw [← native_central_quotient_data_logarithm]
  rfl

end Hindman168
