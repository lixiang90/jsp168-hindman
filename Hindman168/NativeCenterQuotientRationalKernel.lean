import Hindman168.NativeSubgroupRationalCenterKernel
import Hindman168.NativeCenterQuotientRationalSpan
import Hindman168.NativeSubgroupFiniteRationalSpan
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! Exact rational kernel and rank-nullity in the actual original center
quotient. The center part has precisely its actual real dimension for
the specified discrete cocompact lattice. The last theorem is an
explicit induction STEP; it does not claim the full dimension induction. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [Module ℚ E] [LieGroup I ∞ G] [BoundarylessManifold I G]
  [T2Space G] [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G] in
 theorem nativeCenterQuotientProjection_eq_zero_iff (v : E) :
    nativeCenterQuotientProjection (I := I) (G := G) v = 0 ↔
      v ∈ nativeLieCenterModel (I := I) (G := G) :=
  Submodule.Quotient.mk_eq_zero (nativeLieCenterModel (I := I) (G := G))

noncomputable def nativeCenterQuotientRationalLogKernelEquiv (Γ : Subgroup G) :
    LinearMap.ker
      (((nativeCenterQuotientProjection (I := I) (G := G)).toLinearMap.restrictScalars ℚ).domRestrict
        (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)) ≃ₗ[ℚ]
      nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G) where
  toFun := fun v => ⟨v.val.val,
    nativeSubgroupRationalLogSpan_central_mem_intersection Γ v.val.property
      ((nativeCenterQuotientProjection_eq_zero_iff (I := I) (G := G) v.val.val).mp v.property)⟩
  invFun := fun v => ⟨⟨v.val, nativeSubgroupRationalLogSpan_mono inf_le_left v.property⟩,
    (nativeCenterQuotientProjection_eq_zero_iff (I := I) (G := G) v.val).mpr
      (nativeSubgroupRationalLogSpan_center_intersection_le Γ v.property)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

 theorem nativeCenterQuotient_rationalLogSpan_finrank_split (Γ : Subgroup G)
    [FiniteDimensional ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)] :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    Module.finrank ℚ
        (nativeSubgroupRationalLogSpan (E := F) (I := 𝓘(ℝ, F))
          (Γ.map (QuotientGroup.mk' (Subgroup.center G)))) +
      Module.finrank ℚ
        (nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G)) =
      Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  let W := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let π := (nativeCenterQuotientProjection (I := I) (G := G)).toLinearMap.restrictScalars ℚ
  let f := π.domRestrict W
  have hr := (LinearMap.ker f).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange, LinearMap.range_domRestrict] at hr
  rw [nativeCenterQuotient_rationalLogSpan_map] at hr
  rw [(nativeCenterQuotientRationalLogKernelEquiv (E := E) (I := I) Γ).finrank_eq] at hr
  exact hr

 theorem nativeLattice_center_original_rationalLogSpan_finrank (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    Module.finrank ℚ
        (nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G)) =
      Module.finrank ℝ (nativeLieCenterModel (I := I) (G := G)) := by
  let C : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let W := nativeCenterRationalLogSpan (I := I) Γ
  have hm := nativeCenterRationalLogSpan_map_eq_original_span (E := E) (I := I) Γ
  have hf : Module.finrank ℚ (W.map (C.subtype.restrictScalars ℚ)) = Module.finrank ℚ W := by
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (Subtype.val_injective.comp Subtype.val_injective)
  calc
    _ = Module.finrank ℚ (W.map (C.subtype.restrictScalars ℚ)) :=
      congrArg (fun N : Submodule ℚ E => Module.finrank ℚ N) hm.symm
    _ = Module.finrank ℚ W := hf
    _ = _ := nativeCenterRationalLogSpan_finrank (E := E) (I := I) Γ

 theorem nativeLattice_rationalLogSpan_finrank_center_step (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
    letI := nativeCenterQuotient_t2Space (I := I) (G := G)
    letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
    letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
    let F := E ⧸ nativeLieCenterModel (I := I) (G := G)
    Module.finrank ℚ
        (nativeSubgroupRationalLogSpan (E := F) (I := 𝓘(ℝ, F))
          (Γ.map (QuotientGroup.mk' (Subgroup.center G)))) = Module.finrank ℝ F →
      Module.finrank ℚ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) =
        Module.finrank ℝ E := by
  letI := nativeCenterQuotientChartedSpace (I := I) (G := G)
  letI := nativeCenterQuotient_t2Space (I := I) (G := G)
  letI := nativeCenterQuotient_lieGroup (I := I) (G := G)
  letI := nativeCenterQuotient_simplyConnected (I := I) (G := G)
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := E) (I := I) Γ
  dsimp only
  intro hq
  have hr := nativeCenterQuotient_rationalLogSpan_finrank_split (E := E) (I := I) Γ
  dsimp only at hr
  rw [hq, nativeLattice_center_original_rationalLogSpan_finrank] at hr
  exact hr.symm.trans (nativeLieCenterModel (I := I) (G := G)).finrank_quotient_add_finrank

end Hindman168
