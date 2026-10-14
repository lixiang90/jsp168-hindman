import Hindman168.RoughNativeNormalizedObstructionBadFamily
import Hindman168.NativeRationalLieFiltration
import Hindman168.RoughNativeHorizontalCharacterGrid

/-! Actual original nonzero horizontal character gives TRUE rational
normalized pivot, genuine positive lattice power and strict smaller-finrank
canonical kernel data BEFORE all source/scale/length inputs. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_top_lie_rational {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ
      (nativeLieSubalgebraModel (⊤ : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))) := by
  have h := (nativeOriginalRationalLieFiltration D 1 (by omega)).rational 0
  rw [(nativeOriginalRationalLieFiltration D 1 (by omega)).zero] at h
  exact h

theorem native_original_horizontal_top_bracket {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (χ : D.E →ₗ[ℝ] ℝ) (hHor : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) :
    ∀ x ∈ nativeLieSubalgebraModel (⊤ : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G)),
      ∀ y ∈ nativeLieSubalgebraModel (⊤ : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G)),
        χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0 := by
  intro x _ y _
  apply hHor.2.1
  rw [← nativeLieAdjointGenerator_eq_differential]
  exact nativeLieAdjointGenerator_mem_lowerCentral_next x
    (by rw [nativeLieLowerCentralModel_zero]; exact Submodule.mem_top :
      y ∈ nativeLieLowerCentralModel (I := D.I) (G := D.G) 0)

theorem native_original_horizontal_kernel_geometry {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (χ : D.E →ₗ[ℝ] ℝ)
    (hHor : RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) :
    let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
    let hS := native_original_top_lie_rational D
    let hχ := native_original_horizontal_top_bracket D χ hHor
    let hQ := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ hHor.2.2
    ∃ V : D.E, ∃ hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      χ V=1 ∧ ∃ K : ℕ, 0 < K ∧
      nativeLieExponential (I := D.I) (G := D.G) ((K : ℝ) • V) ∈ D.Γ ∧
      ∀ j : Fin K,
        Module.finrank ℝ (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)).E <
          Module.finrank ℝ D.E := by
  let S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) := ⊤
  let hS := native_original_top_lie_rational D
  let hχ := native_original_horizontal_top_bracket D χ hHor
  let hQ := rough_native_integral_character_rational_on_span (I := D.I) D.Γ χ hHor.2.2
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hHor.1
  have hv0 : χ v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
  have hvS : v ∈ nativeLieSubalgebraModel S := by
    change v ∈ (⊤ : Submodule ℝ D.E)
    exact Submodule.mem_top
  obtain ⟨V,_hVS,hVr,hV,K,hK,hPeriod⟩ := rough_native_fixed_character_normalization
    (I := D.I) D.Γ S hS χ hQ hvS hv0
  exact ⟨V,hVr,hV,K,hK,hPeriod,fun j => roughNativeKernelNilmanifold_finrank_lt
    D S hS χ hχ hQ V hVr (j.val : ℤ) hvS hv0⟩

end Hindman168
