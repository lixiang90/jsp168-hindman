import Hindman168.NativeRationalFirstLayerBasis
import Hindman168.NativeLatticeFilteredSmoothBasisCoordinates
import Hindman168.FiniteRationalScalarDenominator

/-! A TRUE geometry-only denominator for the rational split vectors in
the original smooth lattice basis. No exponential of a split vector is
assumed in the lattice. Every original real scalar expansion is proved. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalSplitBasisMatrix {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    (NativeRationalFirstLayerIndex D L × Fin (Module.finrank ℝ D.E)) → ℚ :=
  fun ij => (nativeLatticeFilteredSmoothRationalBasis (I := D.I) D.Γ).equivFun
    (nativeRationalFirstLayerRationalBasis D L (Sum.inr ij.1)) ij.2

noncomputable def nativeRationalSplitBasisDenominator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) : ℕ :=
  Classical.choose (finite_rational_scalar_denominator (nativeRationalSplitBasisMatrix D L))

theorem native_rational_split_basis_denominator_positive {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    0 < nativeRationalSplitBasisDenominator D L :=
  (Classical.choose_spec (finite_rational_scalar_denominator (nativeRationalSplitBasisMatrix D L))).1

theorem native_rational_split_basis_scalar_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (f : D.E →ₗ[ℝ] ℝ) (i : NativeRationalFirstLayerIndex D L) :
    f (nativeRationalFirstLayerRealBasis D L (Sum.inr i)) =
      ∑ j : Fin (Module.finrank ℝ D.E), (nativeRationalSplitBasisMatrix D L (i,j) : ℝ)*
        f (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j) := by
  let b := nativeRationalFirstLayerRealBasis D L (Sum.inr i)
  have hcoord (j : Fin (Module.finrank ℝ D.E)) :
      (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).equivFun b j =
        (nativeRationalSplitBasisMatrix D L (i,j) : ℝ) := by
    dsimp only [b]
    rw [native_rational_first_layer_basis_apply]
    exact congrFun (native_lattice_filtered_smooth_basis_coordinates (I := D.I) D.Γ
      (nativeRationalFirstLayerRationalBasis D L (Sum.inr i))) j
  calc
    _ = f (∑ j, (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).equivFun b j •
        nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j) :=
      congrArg f ((nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ).sum_equivFun b).symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul,hcoord]
      rfl

theorem native_rational_split_basis_scalar_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (f : D.E →ₗ[ℝ] ℝ)
    (hf : ∀ j : Fin (Module.finrank ℝ D.E), ∃ z : ℤ,
      f (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j) = (z : ℝ))
    (i : NativeRationalFirstLayerIndex D L) :
    ∃ z : ℤ, (nativeRationalSplitBasisDenominator D L : ℝ)*
      f (nativeRationalFirstLayerRealBasis D L (Sum.inr i)) = (z : ℝ) := by
  choose z hz using hf
  have hden := (Classical.choose_spec (finite_rational_scalar_denominator
    (nativeRationalSplitBasisMatrix D L))).2
  have hd : ∀ j : Fin (Module.finrank ℝ D.E), ∃ a : ℤ,
      (nativeRationalSplitBasisDenominator D L : ℝ)*(nativeRationalSplitBasisMatrix D L (i,j) : ℝ) = (a : ℝ) :=
    fun j => hden (i,j)
  choose a ha using hd
  refine ⟨∑ j, a j*z j,?_⟩
  rw [native_rational_split_basis_scalar_evaluation,Finset.mul_sum,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc,ha,hz,Int.cast_mul]

end Hindman168
