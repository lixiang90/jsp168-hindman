import Hindman168.NativeRationalFirstLayerBasis
import Hindman168.RationalSubspaceFunctional
import Hindman168.NativeLatticeRationalCharacter

/-! Actual first-layer rational duals kill SAME original F_2. Their real
extension and every rational value are proved, not supplied as data. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFirstLayerFunctional {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) : D.E →ₗ[ℝ] ℝ := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rationalSubspaceFunctional _ (nativeLattice_rationalLogSpan_finrank (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := D.E) (I := D.I) D.Γ)
    ((nativeRationalFirstLayerRationalBasis D L).coord (Sum.inr i))

theorem native_rational_first_layer_functional_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L)
    (w : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRationalFirstLayerFunctional D L i w =
      ((nativeRationalFirstLayerRationalBasis D L).coord (Sum.inr i) w : ℝ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rationalSubspaceFunctional_apply _ _ _ _ w

theorem native_rational_first_layer_functional_basis {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) (j : NativeRationalFirstLayerBasisIndex D L) :
    nativeRationalFirstLayerFunctional D L i (nativeRationalFirstLayerRealBasis D L j) =
      if j=Sum.inr i then 1 else 0 := by
  rw [native_rational_first_layer_basis_apply,native_rational_first_layer_functional_rational,
    Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
  split_ifs <;> simp

theorem native_rational_first_layer_functional_coord {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) :
    nativeRationalFirstLayerFunctional D L i = (nativeRationalFirstLayerRealBasis D L).coord (Sum.inr i) := by
  apply (nativeRationalFirstLayerRealBasis D L).ext
  intro j
  rw [native_rational_first_layer_functional_basis,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]

theorem native_rational_first_layer_functional_kills_two {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerIndex D L) :
    L.layer 2 ≤ (nativeRationalFirstLayerFunctional D L i).ker := by
  rw [← native_rational_first_layer_basis_inl_span D L]
  apply Submodule.span_le.mpr
  rintro v ⟨j,rfl⟩
  change nativeRationalFirstLayerFunctional D L i (nativeRationalFirstLayerRealBasis D L (Sum.inl j)) = 0
  rw [native_rational_first_layer_functional_basis,if_neg (by simp)]

theorem native_rational_kills_two_kills_commutator {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (f : D.E →ₗ[ℝ] ℝ)
    (hf : L.layer 2 ≤ f.ker) : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ f.ker := by
  apply nativeLieFunctional_lowerCentral_le_kernel
  intro v w
  have hv : v ∈ L.layer 1 := by rw [L.one]; exact Submodule.mem_top
  have hw : w ∈ L.layer 1 := by rw [L.one]; exact Submodule.mem_top
  exact hf (L.bracket 1 1 v w hv hw)

end Hindman168
