import Hindman168.NativeCenterLayerFlagBasis
import Hindman168.IntegerLatticeChosenCoordinates
import Hindman168.NativeCenterOrderedCoordinates

namespace Hindman168
open Module
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem native_center_layer_basis_exponential_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    nativeLieExponential (I := I) (G := G)
      (nativeCenterLayerRealBasis (I := I) Γ i).val ∈ Γ := by
  rw [native_center_layer_real_basis_apply]
  exact (nativeCenterLayerIntegerBasis (I := I) Γ i).property

theorem native_center_layer_basis_mem_original_rational_span (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)))) :
    (nativeCenterLayerRealBasis (I := I) Γ i).val ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  have h := nativeSubgroup_logarithm_mem_span (E := E) (I := I) (G := G) Γ
    (native_center_layer_basis_exponential_mem Γ i)
  simpa only [nativeLieGlobalLogarithm_exponential] using h

theorem native_center_layer_exponential_mem_iff_coordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (v : nativeLieCenterModel (I := I) (G := G)) :
    nativeLieExponential (I := I) (G := G) v.val ∈ Γ ↔
      ∀ i, ∃ n : ℤ, (nativeCenterLayerRealBasis (I := I) Γ).repr v i = (n : ℝ) := by
  letI := nativeCenterLogLattice_discrete (E := E) (I := I) Γ
  letI := nativeCenterLogLattice_isZLattice (E := E) (I := I) Γ
  exact integer_lattice_chosen_basis_mem_iff_coordinates
    (nativeCenterLogLattice (I := I) Γ) (nativeCenterLayerIntegerBasis (I := I) Γ) v

noncomputable def nativeCenterLayerCoordinates (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) ≃ₜ
      Subgroup.center G :=
  (nativeCenterLayerRealBasis (I := I) Γ).equivFunL.symm.toHomeomorph.trans
    (nativeLieCenterExponentialHomeomorph (I := I) (G := G))

theorem native_center_layer_coordinates_exponential (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLayerCoordinates (I := I) Γ x : G) =
      nativeLieExponential (I := I) (G := G)
        ((nativeCenterLayerRealBasis (I := I) Γ).equivFun.symm x).val := rfl

theorem native_center_layer_coordinates_mem_iff (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLayerCoordinates (I := I) Γ x : G) ∈ Γ ↔
      ∀ i, ∃ n : ℤ, x i = (n : ℝ) := by
  rw [native_center_layer_coordinates_exponential, native_center_layer_exponential_mem_iff_coordinates]
  change (∀ i, ∃ n : ℤ, ((nativeCenterLayerRealBasis (I := I) Γ).equivFun
    ((nativeCenterLayerRealBasis (I := I) Γ).equivFun.symm x)) i = (n : ℝ)) ↔ _
  rw [LinearEquiv.apply_symm_apply]

theorem native_center_layer_coordinates_ordered_product (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (x : Fin (Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G))) → ℝ) :
    (nativeCenterLayerCoordinates (I := I) Γ x : G) =
      (List.ofFn (fun i => nativeLieExponential (I := I) (G := G)
        (x i • (nativeCenterLayerRealBasis (I := I) Γ i).val))).prod := by
  rw [native_center_layer_coordinates_exponential]
  let b := nativeCenterLayerRealBasis (I := I) Γ
  have he : b.equivFun.symm x = ∑ i, x i • b i := by
    have h := b.sum_equivFun (b.equivFun.symm x)
    rw [b.equivFun.apply_symm_apply x] at h
    exact h.symm
  rw [he]
  have h := native_center_exponential_list_sum (I := I) (G := G) (List.ofFn (fun i => x i • b i))
  simpa only [List.sum_ofFn, List.map_ofFn, Function.comp_def, Submodule.coe_smul, b] using h

end Hindman168
