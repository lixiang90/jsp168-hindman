import Hindman168.NativeRationalFirstLayerFunctional
import Hindman168.FiniteRationalScalarDenominator
import Hindman168.NativeFilteredSmoothBasisCharacterIntegrality

/-! ONE actual common denominator, fixed by D/L, makes EVERY true
first-layer coordinate integral on the SAME original lattice. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFirstLayerMatrix {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    (NativeRationalFirstLayerIndex D L × Fin (Module.finrank ℝ D.E)) → ℚ :=
  fun ij => (nativeRationalFirstLayerRationalBasis D L).coord (Sum.inr ij.1)
    ⟨nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ ij.2,
      native_lattice_filtered_smooth_basis_mem_rational_span (I := D.I) D.Γ ij.2⟩

noncomputable def nativeRationalFirstLayerDenominator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) : ℕ :=
  Classical.choose (finite_rational_scalar_denominator (nativeRationalFirstLayerMatrix D L))

theorem native_rational_first_layer_denominator_positive {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    0 < nativeRationalFirstLayerDenominator D L :=
  (Classical.choose_spec (finite_rational_scalar_denominator (nativeRationalFirstLayerMatrix D L))).1

noncomputable def nativeRationalFirstLayerCoordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) : D.E →ₗ[ℝ] ℝ :=
  (nativeRationalFirstLayerDenominator D L : ℝ) • nativeRationalFirstLayerFunctional D L i

theorem native_rational_first_layer_coordinate_kills_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) : L.layer 2 ≤ (nativeRationalFirstLayerCoordinate D L i).ker := by
  intro v hv
  change (nativeRationalFirstLayerDenominator D L : ℝ)*nativeRationalFirstLayerFunctional D L i v=0
  rw [native_rational_first_layer_functional_kills_two D L i hv,mul_zero]

theorem native_rational_first_layer_coordinate_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) (g : D.G) (hg : g ∈ D.Γ) :
    ∃ z : ℤ, nativeRationalFirstLayerCoordinate D L i
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ) := by
  have hHor := native_rational_kills_two_kills_commutator D L _
    (native_rational_first_layer_coordinate_kills_two D L i)
  apply (native_filtered_smooth_basis_character_integral_iff (I := D.I) D.Γ _ hHor).mpr ?_ g hg
  intro j
  have he := (Classical.choose_spec (finite_rational_scalar_denominator (nativeRationalFirstLayerMatrix D L))).2 (i,j)
  change ∃ z : ℤ, (nativeRationalFirstLayerDenominator D L : ℝ)*nativeRationalFirstLayerFunctional D L i
    (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j) = (z : ℝ)
  rw [native_rational_first_layer_functional_rational D L i
    ⟨nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ j,
      native_lattice_filtered_smooth_basis_mem_rational_span (I := D.I) D.Γ j⟩]
  exact he

end Hindman168
