import Hindman168.NativeLatticeOrderedSmoothRationalBasis
import Hindman168.RationalCoordinateDecomposition
import Hindman168.NativeSubgroupBracketSpan

/-! The fixed ordered lattice real basis and the rational basis have the same
original columns. Their coordinate square commutes, and rationality of the
coordinates characterizes the original rational logarithmic span. -/

namespace Hindman168
open Module Set
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_lattice_ordered_smooth_basis_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (w : nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).equivFun (w : E) =
      rationalCoordinateCast (Fin (Module.finrank ℝ E))
        ((nativeLatticeOrderedSmoothRationalBasis (I := I) Γ).equivFun w) := by
  apply (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Basis.equivFun_symm_apply]
  have he := congrArg (fun z : nativeSubgroupRationalLogSpan (E := E) (I := I) Γ => (z : E))
    ((nativeLatticeOrderedSmoothRationalBasis (I := I) Γ).sum_equivFun w)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  symm
  calc
    _ = ∑ i, ((nativeLatticeOrderedSmoothRationalBasis (I := I) Γ).equivFun w i) •
        (nativeLatticeOrderedSmoothRationalBasis (I := I) Γ i : E) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [native_lattice_ordered_smooth_rational_basis_apply]
      exact Rat.cast_smul_eq_qsmul ℝ _ _
    _ = (w : E) := he

theorem native_lattice_ordered_smooth_basis_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (v : E) :
    v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ↔
      (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).equivFun v ∈
        range (rationalCoordinateCast (Fin (Module.finrank ℝ E))) := by
  constructor
  · intro hv
    exact ⟨(nativeLatticeOrderedSmoothRationalBasis (I := I) Γ).equivFun ⟨v, hv⟩,
      (native_lattice_ordered_smooth_basis_coordinates Γ ⟨v, hv⟩).symm⟩
  · rintro ⟨q, hq⟩
    let w := (nativeLatticeOrderedSmoothRationalBasis (I := I) Γ).equivFun.symm q
    have he := native_lattice_ordered_smooth_basis_coordinates Γ w
    rw [LinearEquiv.apply_symm_apply] at he
    have hwv : (w : E) = v :=
      (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).equivFun.injective (he.trans hq)
    exact hwv ▸ w.property

theorem native_lattice_ordered_smooth_basis_mem_iff_each_coordinate (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (v : E) :
    v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ↔
      ∀ i, ∃ q : ℚ, (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).repr v i = (q : ℝ) := by
  rw [native_lattice_ordered_smooth_basis_mem_iff_coordinates Γ v]
  constructor
  · rintro ⟨q, hq⟩ i
    exact ⟨q i, (congrFun hq i).symm⟩
  · intro h
    classical
    choose q hq using h
    exact ⟨q, funext fun i => (hq i).symm⟩

theorem native_lattice_ordered_smooth_differential_coordinates_rational (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i j k : Fin (Module.finrank ℝ E)) :
    ∃ q : ℚ, (nativeLatticeOrderedSmoothRealBasis (I := I) Γ).repr
      (nativeLieAdjointDifferential (I := I) (G := G)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ i)
        (nativeLatticeOrderedSmoothRealBasis (I := I) Γ j)) k = (q : ℝ) := by
  exact (native_lattice_ordered_smooth_basis_mem_iff_each_coordinate Γ _).mp
    (nativeSubgroupRationalLogSpan_differential_mem Γ
      (native_lattice_ordered_smooth_basis_mem_rational_span Γ i)
      (native_lattice_ordered_smooth_basis_mem_rational_span Γ j)) k

end Hindman168
