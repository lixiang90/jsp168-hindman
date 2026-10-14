import Hindman168.NativeRationalLieFiltration
import Hindman168.RationalSubspaceSplitBasis
import Hindman168.NativeLatticeFilteredSmoothRationalBasis

/-! TRUE rational basis split at the ACTUAL filtration layer F_2, not only
at the lower central commutator layer. All geometry is fixed by D/L. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalFirstLayerSubspace {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Submodule ℚ (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :=
  ((L.layer 2).restrictScalars ℚ).comap (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ).subtype

noncomputable def nativeRationalFirstLayerComplement {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Submodule ℚ (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :=
  Classical.choose (nativeRationalFirstLayerSubspace D L).exists_isCompl

theorem native_rational_first_layer_complement {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    IsCompl (nativeRationalFirstLayerSubspace D L) (nativeRationalFirstLayerComplement D L) :=
  Classical.choose_spec (nativeRationalFirstLayerSubspace D L).exists_isCompl

noncomputable abbrev NativeRationalFirstLayerIndex {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :=
  Fin (Module.finrank ℚ (nativeRationalFirstLayerComplement D L))

noncomputable abbrev NativeRationalFirstLayerBasisIndex {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :=
  Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L)) ⊕ NativeRationalFirstLayerIndex D L

noncomputable def nativeRationalFirstLayerRationalBasis {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Basis (NativeRationalFirstLayerBasisIndex D L) ℚ
      (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rationalSubspaceSplitBasis _ _ _ (native_rational_first_layer_complement D L)

noncomputable def nativeRationalFirstLayerRealBasis {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Basis (NativeRationalFirstLayerBasisIndex D L) ℝ D.E := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rationalSubspaceRealSplitBasis _ (nativeLattice_rationalLogSpan_finrank (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := D.E) (I := D.I) D.Γ) _ _
    (native_rational_first_layer_complement D L)

theorem native_rational_first_layer_basis_apply {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : NativeRationalFirstLayerBasisIndex D L) :
    nativeRationalFirstLayerRealBasis D L i = (nativeRationalFirstLayerRationalBasis D L i : D.E) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rational_subspace_real_basis_of_basis_apply _ _ _ _ i

theorem native_rational_first_layer_basis_inl_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (i : Fin (Module.finrank ℚ (nativeRationalFirstLayerSubspace D L))) :
    nativeRationalFirstLayerRealBasis D L (Sum.inl i) ∈ L.layer 2 := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rational_subspace_real_split_basis_inl_mem _ _ _ _ _ _ i

theorem native_rational_first_layer_basis_inl_span {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    Submodule.span ℝ (Set.range (fun i => nativeRationalFirstLayerRealBasis D L (Sum.inl i))) = L.layer 2 := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  exact rational_subspace_real_split_basis_inl_span _ _ _ _ (L.rational 2) _ _

end Hindman168
