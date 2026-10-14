import Hindman168.NativeCentralCharacterPullback
import Hindman168.NativeContinuousHorizontalCharacter

/-! Genuine horizontal property and original lattice integrality of the
actual child character pullback, without a parent-character assumption. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_central_character_pullback_mul {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeCentralQuotientData D).I)
      (G := (nativeCentralQuotientData D).G) 1 ≤ χ.toLinearMap.ker) (g h : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeCentralCharacterPullback D χ).toLinearMap (g*h) =
      nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeCentralCharacterPullback D χ).toLinearMap g +
      nativeLieLogarithmCharacter (I := D.I) (G := D.G)
        (nativeCentralCharacterPullback D χ).toLinearMap h := by
  rw [native_central_character_pullback_log, native_central_character_pullback_log,
    native_central_character_pullback_log]
  rw [show (↑(g*h) : D.G ⧸ Subgroup.center D.G) =
    (↑g : D.G ⧸ Subgroup.center D.G) * (↑h : D.G ⧸ Subgroup.center D.G) from
      (QuotientGroup.mk' (Subgroup.center D.G)).map_mul g h]
  exact nativeLieLogarithmCharacter_mul (I := (nativeCentralQuotientData D).I)
      (G := (nativeCentralQuotientData D).G) χ.toLinearMap hχ
        (g : D.G ⧸ Subgroup.center D.G) (h : D.G ⧸ Subgroup.center D.G)

theorem native_central_character_pullback_commutator {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeCentralQuotientData D).I)
      (G := (nativeCentralQuotientData D).G) 1 ≤ χ.toLinearMap.ker) :
    nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤
      (nativeCentralCharacterPullback D χ).toLinearMap.ker :=
  native_continuous_character_linearization_horizontal (I := D.I)
    (nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeCentralCharacterPullback D χ).toLinearMap)
    (native_central_character_pullback_mul D χ hχ) (nativeCentralCharacterPullback D χ)
    (fun _ => rfl)

theorem native_central_character_pullback_lattice {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : ∀ γ ∈ (nativeCentralQuotientData D).Γ, ∃ m : ℤ,
      χ (nativeLieGlobalLogarithm (E := (nativeCentralQuotientData D).E)
        (I := (nativeCentralQuotientData D).I) (G := (nativeCentralQuotientData D).G) γ) = (m : ℝ)) :
    ∀ γ ∈ D.Γ, ∃ m : ℤ,
      nativeCentralCharacterPullback D χ
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ) = (m : ℝ) := by
  intro γ hγ
  have hγ' : (γ : D.G ⧸ Subgroup.center D.G) ∈ (nativeCentralQuotientData D).Γ :=
    Subgroup.mem_map.mpr ⟨γ,hγ,rfl⟩
  obtain ⟨m,hm⟩ := hχ _ hγ'
  refine ⟨m, ?_⟩
  rw [native_central_quotient_data_logarithm] at hm
  exact hm

theorem native_central_character_pullback_horizontal {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : (nativeCentralQuotientData D).E →L[ℝ] ℝ)
    (hχ : RoughNativeHorizontalFunctional (E := (nativeCentralQuotientData D).E)
      (I := (nativeCentralQuotientData D).I) (nativeCentralQuotientData D).Γ χ.toLinearMap) :
    RoughNativeHorizontalFunctional (E := D.E) (I := D.I) D.Γ
      (nativeCentralCharacterPullback D χ).toLinearMap := by
  refine ⟨?_, native_central_character_pullback_commutator D χ hχ.2.1,
    native_central_character_pullback_lattice D χ hχ.2.2⟩
  intro hz
  apply hχ.1
  ext v
  have h := DFunLike.congr_fun hz (nativeCenterQuotientSection (I := D.I) (G := D.G) v)
  simpa only [ContinuousLinearMap.coe_coe, native_central_character_pullback_apply,
    nativeCenterQuotientSection_right, LinearMap.zero_apply] using h

end Hindman168
