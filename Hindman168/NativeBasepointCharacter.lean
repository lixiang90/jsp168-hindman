import Hindman168.RoughGroupBasepointNormalization
import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLieLogarithmCharacter
import Mathlib.Tactic.Linarith

/-! Actual original horizontal real characters under original basepoint
normalization differ by precisely the original constant value. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_character_value {s : ℕ} {V : Type*} [AddCommMonoid V]
    (D : NativeNilmanifoldData.{u} s) (f : D.E →ₗ[ℝ] ℝ)
    (hf : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker)
    (P : V → D.G) (r : D.G) (x : V) :
    f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (roughGroupBasepointNormalization P r x)) =
    f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (P x)) -
      f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (P 0)) := by
  let χ := nativeLieLogarithmCharacter (I := D.I) (G := D.G) f
  have hm : ∀ g h : D.G, χ (g*h) = χ g + χ h :=
    nativeLieLogarithmCharacter_mul f hf
  have h1 : χ 1 = 0 := by
    change f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) 1) = 0
    rw [nativeLieGlobalLogarithm_one,map_zero]
  have hi : ∀ g : D.G, χ g⁻¹ = -χ g := by
    intro g
    have h := hm g g⁻¹
    rw [mul_inv_cancel,h1] at h
    linarith only [h]
  change χ (roughGroupBasepointNormalization P r x) = χ (P x) - χ (P 0)
  simp only [roughGroupBasepointNormalization,hm,hi]
  ring

end Hindman168
