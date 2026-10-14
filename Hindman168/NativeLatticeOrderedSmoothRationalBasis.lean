import Hindman168.NativeLatticeOrderedDiffeomorph
import Hindman168.NativeLatticeRationalForm

namespace Hindman168
open Module
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLatticeOrderedSmoothRationalColumns (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Fin (Module.finrank ℝ E) → nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  fun i => ⟨nativeLatticeOrderedSmoothRealBasis (I := I) Γ i, native_lattice_ordered_smooth_basis_mem_rational_span Γ i⟩

theorem native_lattice_ordered_smooth_rational_columns_independent (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    LinearIndependent ℚ (nativeLatticeOrderedSmoothRationalColumns (I := I) Γ) := by
  apply LinearIndependent.of_comp (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).subtype
  exact (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).linearIndependent.restrict_scalars' ℚ

noncomputable def nativeLatticeOrderedSmoothRationalBasis (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Basis (Fin (Module.finrank ℝ E)) ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  exact basisOfLinearIndependentOfCardEqFinrank' (nativeLatticeOrderedSmoothRationalColumns (I := I) Γ)
    (native_lattice_ordered_smooth_rational_columns_independent Γ)
    (by rw [Fintype.card_fin, nativeLattice_rationalLogSpan_finrank (E := E) (I := I) Γ])

theorem native_lattice_ordered_smooth_rational_basis_apply (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (i : Fin (Module.finrank ℝ E)) :
    (nativeLatticeOrderedSmoothRationalBasis (I := I) Γ i : E) = nativeLatticeOrderedSmoothRealBasis (I := I) Γ i := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  unfold nativeLatticeOrderedSmoothRationalBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

end Hindman168
