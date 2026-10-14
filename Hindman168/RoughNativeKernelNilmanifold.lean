import Hindman168.RoughNativeSubgroupNilmanifold
import Hindman168.RoughNativeFixedKernel

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeKernelNilmanifold {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) : NativeNilmanifoldData.{u} s := by
  have hT : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ
      (nativeLieSubalgebraModel (nativeLieCharacterKernel S χ hχ)) := by
    rw [nativeLieCharacterKernel_model]
    exact rationalRestrictedKernel_rational _ _ χ hS hQ
  have hj : (j : ℝ) • V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ := by
    simpa only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_intCast] using
      (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ).smul_mem (j : ℚ) hV
  exact roughNativeSubgroupNilmanifold D (nativeLieCharacterKernel S χ hχ) hT ((j : ℝ) • V) hj

theorem roughNativeKernelNilmanifold_finrank_lt {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) {v : D.E} (hv : v ∈ nativeLieSubalgebraModel S) (hχv : χ v ≠ 0) :
    Module.finrank ℝ (roughNativeKernelNilmanifold D S hS χ hχ hQ V hV j).E <
      Module.finrank ℝ D.E := by
  change Module.finrank ℝ (nativeLieSubalgebraModel (nativeLieCharacterKernel S χ hχ)) < _
  exact ((rough_native_fixed_kernel_rational_dimension D.Γ S hS χ hχ hQ hv hχv).2).trans_le
    (Submodule.finrank_le (nativeLieSubalgebraModel S))

theorem roughNativeKernelNilmanifold_group {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) :
    (roughNativeKernelNilmanifold D S hS χ hχ hQ V hV j).G =
      nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ) := rfl

theorem roughNativeKernelNilmanifold_lattice {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) :
    (roughNativeKernelNilmanifold D S hS χ hχ hQ V hV j).Γ =
      (roughConjugateSubgroup D.Γ (nativeLieExponential (I := D.I) (G := D.G) ((j : ℝ) • V))).comap
        (nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ)).subtype := rfl

end Hindman168
