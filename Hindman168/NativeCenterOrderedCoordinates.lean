import Hindman168.NativeCenterLatticeCoordinates
import Mathlib.Algebra.BigOperators.Fin

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem native_center_exponential_list_sum
    (l : List (nativeLieCenterModel (I := I) (G := G))) :
    nativeLieExponential (I := I) (G := G) l.sum.val =
      (l.map (fun v => nativeLieExponential (I := I) (G := G) v.val)).prod := by
  induction l with
  | nil => exact nativeLieExponential_zero (I := I) (G := G)
  | cons v l ih =>
    change nativeLieExponential (I := I) (G := G) (v.val+l.sum.val) =
      nativeLieExponential (I := I) (G := G) v.val * _
    rw [nativeLieExponential_add_of_mem_centerModel v.property, ih]
    rfl

theorem native_center_lattice_coordinates_ordered_product (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLatticeCoordinates (I := I) Γ x : G) =
      (List.ofFn (fun i => nativeLieExponential (I := I) (G := G)
        (x i • (nativeCenterLatticeRealBasis (I := I) Γ i).val))).prod := by
  rw [native_center_lattice_coordinates_exponential]
  let b := nativeCenterLatticeRealBasis (I := I) Γ
  have he : b.equivFun.symm x = ∑ i, x i • b i := by
    have h := b.sum_equivFun (b.equivFun.symm x)
    rw [b.equivFun.apply_symm_apply x] at h
    exact h.symm
  rw [he]
  have h := native_center_exponential_list_sum (I := I) (G := G)
    (List.ofFn (fun i => x i • b i))
  simpa only [List.sum_ofFn, List.map_ofFn, Function.comp_def, Submodule.coe_smul, b] using h

theorem native_center_lattice_basis_mem_original_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    (nativeCenterLatticeRealBasis (I := I) Γ i).val ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  have h := nativeSubgroup_logarithm_mem_span (E := E) (I := I) (G := G) Γ
    (native_center_lattice_basis_exponential_mem Γ i)
  simpa only [nativeLieGlobalLogarithm_exponential] using h

end Hindman168
