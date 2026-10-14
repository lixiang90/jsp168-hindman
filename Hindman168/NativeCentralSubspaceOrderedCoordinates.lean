import Hindman168.NativeCentralSubspaceLatticeCoordinates
import Mathlib.Algebra.BigOperators.Fin

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] nativeCentralSubspaceSubgroup_normal

omit [Module ℚ E] [Group.IsNilpotent G] [FiniteDimensional ℝ E]
  [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem native_central_subspace_exponential_list_sum
    (V : Submodule ℝ E) (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (l : List V) :
    nativeLieExponential (I := I) (G := G) l.sum.val =
      (l.map (fun v => nativeLieExponential (I := I) (G := G) v.val)).prod := by
  induction l with
  | nil => exact nativeLieExponential_zero (I := I) (G := G)
  | cons v l ih =>
    change nativeLieExponential (I := I) (G := G) (v.val+l.sum.val) =
      nativeLieExponential (I := I) (G := G) v.val * _
    rw [nativeLieExponential_add_of_mem_centerModel (hV v.property), ih]
    rfl

theorem native_central_subspace_lattice_coordinates_ordered_product (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (x : Fin (Module.finrank ℝ (V)) → ℝ) :
    (nativeCentralSubspaceLatticeCoordinates (I := I) Γ V hV hrat x : G) =
      (List.ofFn (fun i => nativeLieExponential (I := I) (G := G)
        (x i • (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val))).prod := by
  rw [native_central_subspace_lattice_coordinates_exponential (I := I) Γ V hV hrat]
  let b := nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat
  have he : b.equivFun.symm x = ∑ i, x i • b i := by
    have h := b.sum_equivFun (b.equivFun.symm x)
    rw [b.equivFun.apply_symm_apply x] at h
    exact h.symm
  rw [he]
  have h := native_central_subspace_exponential_list_sum (I := I) (G := G) V hV
    (List.ofFn (fun i => x i • b i))
  simpa only [List.sum_ofFn, List.map_ofFn, Function.comp_def, Submodule.coe_smul, b] using h

theorem native_central_subspace_lattice_basis_mem_original_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] (V : Submodule ℝ E) [IsClosed (V : Set E)]
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G))
    (hrat : nativeLatticeRationalSubspace (E := E) (I := I) Γ V)
    (i : Fin (Module.finrank ℝ (V))) :
    (nativeCentralSubspaceLatticeRealBasis (I := I) Γ V hV hrat i).val ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  have h := nativeSubgroup_logarithm_mem_span (E := E) (I := I) (G := G) Γ
    (native_central_subspace_lattice_basis_exponential_mem (I := I) Γ V hV hrat i)
  simpa only [nativeLieGlobalLogarithm_exponential] using h

end Hindman168
