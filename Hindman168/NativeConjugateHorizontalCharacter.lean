import Hindman168.NativeConjugateNilmanifoldData
import Hindman168.RoughNativeHorizontalCharacterGrid

/-! Actual original horizontal logarithmic characters are conjugation
invariant. TRUE lattice integrality/nonzeroness and bounded ORIGINAL grid
membership transfer from conjugated native data back to original data. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_conjugate_horizontal_character_value {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ χ.ker) (ρ g : D.G) :
    χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (ρ*g*ρ⁻¹))=
      χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) := by
  let f := nativeLieLogarithmCharacter (E := D.E) (I := D.I) (G := D.G) χ
  have hm : ∀ x y : D.G, f (x*y)=f x+f y := nativeLieLogarithmCharacter_mul χ hχ
  have h0 : f 1=0 := by
    change χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) 1)=0
    rw [nativeLieGlobalLogarithm_one,map_zero]
  have hi := hm ρ ρ⁻¹
  rw [mul_inv_cancel,h0] at hi
  change f (ρ*g*ρ⁻¹)=f g
  rw [hm,hm]
  linarith

theorem native_conjugate_horizontal_functional_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) (χ : D.E →ₗ[ℝ] ℝ) :
    RoughNativeHorizontalFunctional (I := D.I) (roughConjugateSubgroup D.Γ ρ) χ ↔
      RoughNativeHorizontalFunctional (I := D.I) D.Γ χ := by
  constructor
  · intro h
    refine ⟨h.1,h.2.1,?_⟩
    intro γ hγ
    obtain ⟨m,hm⟩ := h.2.2 (ρ*γ*ρ⁻¹) ((roughConjugateSubgroup_mem D.Γ ρ γ).mpr hγ)
    exact ⟨m,(native_conjugate_horizontal_character_value D χ h.2.1 ρ γ).symm.trans hm⟩
  · intro h
    refine ⟨h.1,h.2.1,?_⟩
    intro γ hγ
    obtain ⟨g,hg,rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨m,hm⟩ := h.2.2 g hg
    exact ⟨m,(native_conjugate_horizontal_character_value D χ h.2.1 ρ g).trans hm⟩

theorem native_conjugate_horizontal_original_grid {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (ρ : D.G) (χ : D.E →L[ℝ] ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hNorm : ‖χ‖ ≤ A) (hHor : RoughNativeHorizontalFunctional (I := D.I)
      (roughConjugateSubgroup D.Γ ρ) χ.toLinearMap) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ A :=
  rough_native_norm_bounded_horizontal_grid_mem D.Γ A hA χ hNorm
    ((native_conjugate_horizontal_functional_iff D ρ χ.toLinearMap).mp hHor)

end Hindman168
