import Hindman168.NativeRationalFirstLayerCoordinates

/-! Every REAL functional killing ACTUAL F_2 is exactly represented in
the true first-layer coordinates, with the geometry-only denominator. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_first_layer_functional_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (f : D.E →ₗ[ℝ] ℝ) (hf : L.layer 2 ≤ f.ker) (v : D.E) :
    f v = ∑ i : NativeRationalFirstLayerIndex D L,
      f (nativeRationalFirstLayerRealBasis D L (Sum.inr i))*nativeRationalFirstLayerFunctional D L i v := by
  have he := congrArg f ((nativeRationalFirstLayerRealBasis D L).sum_repr v)
  rw [map_sum,Fintype.sum_sum_type] at he
  have hz : (∑ i : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L)),
      f ((nativeRationalFirstLayerRealBasis D L).repr v (Sum.inl i) •
        nativeRationalFirstLayerRealBasis D L (Sum.inl i)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    have hi := hf (native_rational_first_layer_basis_inl_mem D L i)
    change f (nativeRationalFirstLayerRealBasis D L (Sum.inl i))=0 at hi
    rw [hi,smul_zero]
  rw [hz,zero_add] at he
  simp only [map_smul,smul_eq_mul] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [native_rational_first_layer_functional_coord,Basis.coord_apply]
  exact mul_comm _ _

theorem native_rational_first_layer_character_evaluation {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (f : D.E →ₗ[ℝ] ℝ) (hf : L.layer 2 ≤ f.ker) (g : D.G) :
    nativeLieLogarithmCharacter (I := D.I) (G := D.G) f g =
      ∑ i : NativeRationalFirstLayerIndex D L,
        (f (nativeRationalFirstLayerRealBasis D L (Sum.inr i))/(nativeRationalFirstLayerDenominator D L : ℝ))*
          nativeRationalFirstLayerCoordinates D L g i := by
  have hq : (nativeRationalFirstLayerDenominator D L : ℝ) ≠ 0 := by
    exact_mod_cast (native_rational_first_layer_denominator_positive D L).ne'
  rw [show nativeLieLogarithmCharacter (I := D.I) (G := D.G) f g =
      f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) from rfl,
    native_rational_first_layer_functional_evaluation D L f hf]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (f (nativeRationalFirstLayerRealBasis D L (Sum.inr i))/(nativeRationalFirstLayerDenominator D L : ℝ))*
    ((nativeRationalFirstLayerDenominator D L : ℝ)*nativeRationalFirstLayerFunctional D L i _)
  field_simp [hq]

end Hindman168
