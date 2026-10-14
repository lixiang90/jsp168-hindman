import Hindman168.NativeConjugateHorizontalCharacter
import Hindman168.RoughNativeCharacterMultiplier

/-! A TRUE positive natural multiplier preserves actual ORIGINAL nonzero
horizontal lattice integrality, with a proved norm and original grid budget. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_horizontal_positive_natural_multiple {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) (M : ℕ) (hM : 0 < M) :
    RoughNativeHorizontalFunctional (I := D.I) D.Γ ((M : ℝ) • χ) := by
  refine ⟨smul_ne_zero (by exact_mod_cast hM.ne') hχ.1,?_,?_⟩
  · intro v hv
    change (M : ℝ)*χ v=0
    have hz := hχ.2.1 hv
    change χ v=0 at hz
    rw [hz,mul_zero]
  · intro g hg
    obtain ⟨z,hz⟩ := hχ.2.2 g hg
    refine ⟨(M : ℤ)*z,?_⟩
    change (M : ℝ)*χ (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g)=_
    rw [hz,Int.cast_mul,Int.cast_natCast]

theorem native_horizontal_natural_multiple_norm {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (χ : D.E →L[ℝ] ℝ) (M : ℕ) :
    ‖(M : ℝ) • χ‖=(M : ℝ)*‖χ‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

theorem native_horizontal_natural_multiple_original_grid {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (χ : D.E →L[ℝ] ℝ)
    (hχ : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ.toLinearMap)
    (M : ℕ) (hM : 0 < M) (A : ℝ) (hA : 0 ≤ A) (hNorm : ‖χ‖ ≤ A) :
    ((M : ℝ) • χ).toLinearMap ∈ roughNativeHorizontalCharacterGrid (I := D.I) D.Γ ((M : ℝ)*A) := by
  apply rough_native_norm_bounded_horizontal_grid_mem D.Γ ((M : ℝ)*A) (by positivity)
  · rw [native_horizontal_natural_multiple_norm D χ M]
    exact mul_le_mul_of_nonneg_left hNorm (Nat.cast_nonneg M)
  · exact native_horizontal_positive_natural_multiple D χ.toLinearMap hχ M hM

end Hindman168
