import Hindman168.RationalSubspaceSplitBasis
import Hindman168.NativeLieLayerLatticeCompact

namespace Hindman168
open Module
open scoped Manifold ContDiff Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeCommutatorRationalSubspace (Γ : Subgroup G) :
    Submodule ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :=
  ((nativeLieLowerCentralModel (I := I) (G := G) 1).restrictScalars ℚ).comap
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).subtype

noncomputable def roughNativeCommutatorComplement (Γ : Subgroup G) :
    Submodule ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :=
  Classical.choose (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ).exists_isCompl

theorem rough_native_commutator_complement (Γ : Subgroup G) :
    IsCompl (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ)
      (roughNativeCommutatorComplement (E := E) (I := I) Γ) :=
  Classical.choose_spec (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ).exists_isCompl

noncomputable abbrev RoughNativeCommutatorBasisIndex (Γ : Subgroup G) :=
  Fin (Module.finrank ℚ (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ)) ⊕
    Fin (Module.finrank ℚ (roughNativeCommutatorComplement (E := E) (I := I) Γ))

noncomputable def roughNativeCommutatorBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (RoughNativeCommutatorBasisIndex (E := E) (I := I) Γ) ℝ E := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rationalSubspaceRealSplitBasis _ (nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := E) (I := I) Γ) _ _
    (rough_native_commutator_complement (E := E) (I := I) Γ)

theorem rough_native_commutator_basis_rational (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : RoughNativeCommutatorBasisIndex (E := E) (I := I) Γ) :
    roughNativeCommutatorBasis (E := E) (I := I) Γ i ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rational_subspace_real_split_basis_rational _ _ _ _ _ _ i

theorem rough_native_commutator_basis_inl_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℚ (roughNativeCommutatorRationalSubspace (E := E) (I := I) Γ))) :
    roughNativeCommutatorBasis (E := E) (I := I) Γ (Sum.inl i) ∈
      nativeLieLowerCentralModel (I := I) (G := G) 1 := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rational_subspace_real_split_basis_inl_mem _ _ _ _ _ _ i

theorem rough_native_commutator_basis_inl_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Submodule.span ℝ (Set.range (fun i =>
      roughNativeCommutatorBasis (E := E) (I := I) Γ (Sum.inl i))) =
        nativeLieLowerCentralModel (I := I) (G := G) 1 := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact rational_subspace_real_split_basis_inl_span _ _ _ _
    (nativeLieLowerCentralModel_lattice_rational Γ 1) _ _

noncomputable def roughNativeCommutatorHorizontalIndices (Γ : Subgroup G) :
    Finset (RoughNativeCommutatorBasisIndex (E := E) (I := I) Γ) :=
  Finset.univ.image Sum.inr

theorem rough_native_commutator_basis_outside_horizontal (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : RoughNativeCommutatorBasisIndex (E := E) (I := I) Γ)
    (hi : i ∉ roughNativeCommutatorHorizontalIndices (E := E) (I := I) Γ) :
    roughNativeCommutatorBasis (E := E) (I := I) Γ i ∈
      nativeLieLowerCentralModel (I := I) (G := G) 1 := by
  cases i with
  | inl i => exact rough_native_commutator_basis_inl_mem Γ i
  | inr i => exact False.elim (hi (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

end Hindman168
