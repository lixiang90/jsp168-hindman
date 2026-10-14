import Hindman168.NativeCenterRationalInclusion
import Hindman168.RationalSpanPositiveDenominators
import Hindman168.NativeCentralPowerRoots
import Hindman168.NativeSubgroupRationalHull

/-! The actual specified center lattice rational span is exactly the
logarithms of the actual central positive roots of the specified
subgroup. Positive integer denominator clearing takes place in the
actual additive center, never in the nonabelian full logarithm set.
The resulting actual central subgroup rational hull equals those roots. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G]
  [SimplyConnectedSpace G] in
theorem nativeCenterRationalLogSpan_mem_iff_positive_root (Γ : Subgroup G)
    (v : nativeLieCenterModel (I := I) (G := G)) :
    v ∈ nativeCenterRationalLogSpan (I := I) Γ ↔
      nativeLieExponential (I := I) (G := G) v.val ∈ positiveSubgroupRoots Γ := by
  let L := nativeCenterLogLattice (I := I) Γ
  have hi := rationalSpan_mem_iff_positive_nat_multiple L v
  constructor
  · intro hv
    obtain ⟨n, hn, hnv⟩ := hi.mp hv
    have hexp : nativeLieExponential (I := I) (G := G) ((n : ℝ) • v.val) ∈ Γ := by
      rw [Nat.cast_smul_eq_nsmul]
      exact hnv
    exact ⟨n, hn, (nativeLieExponential_nat_smul (I := I) (G := G) v.val n) ▸ hexp⟩
  · rintro ⟨n, hn, hgn⟩
    apply hi.mpr
    refine ⟨n, hn, ?_⟩
    have hexp : nativeLieExponential (I := I) (G := G) ((n : ℝ) • v.val) ∈ Γ :=
      (nativeLieExponential_nat_smul (I := I) (G := G) v.val n).symm ▸ hgn
    rw [Nat.cast_smul_eq_nsmul] at hexp
    exact hexp

theorem nativeCenter_original_logSpan_mem_iff_central_roots (Γ : Subgroup G) (g : G) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G) ↔
        g ∈ centralPositiveRootSubgroup Γ := by
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let C : Submodule ℚ V := nativeCenterRationalLogSpan (I := I) Γ
  have hm := nativeCenterRationalLogSpan_map_eq_original_span (I := I) (G := G) Γ
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
    span ℚ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
      (Γ ⊓ Subgroup.center G : Subgroup G)) ↔ _
  rw [← hm]
  constructor
  · rintro ⟨v, hv, hvg⟩
    have he : nativeLieExponential (I := I) (G := G) v.val = g :=
      (congrArg (fun w : E => nativeLieExponential (I := I) (G := G) w) hvg).trans
        (nativeLieExponential_globalLogarithm (I := I) (G := G) g)
    have hr := (nativeCenterRationalLogSpan_mem_iff_positive_root (I := I) (G := G) Γ v).mp hv
    have hc := (nativeLieExponential_mem_center_iff_mem_centerModel (I := I) (G := G) v.val).mpr v.property
    exact he ▸ ⟨hr, hc⟩
  · intro hg
    let v : V := ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g,
      (nativeLieGlobalLogarithm_mem_centerModel_iff (I := I) (G := G) g).mpr hg.2⟩
    have he : nativeLieExponential (I := I) (G := G) v.val = g :=
      nativeLieExponential_globalLogarithm (I := I) (G := G) g
    have hv : v ∈ C :=
      (nativeCenterRationalLogSpan_mem_iff_positive_root (I := I) (G := G) Γ v).mpr (he.symm ▸ hg.1)
    exact ⟨v, hv, rfl⟩

theorem nativeCenter_intersection_rationalHull_eq_positiveRoots (Γ : Subgroup G) :
    nativeSubgroupRationalHull (E := E) (I := I) (Γ ⊓ Subgroup.center G) =
      centralPositiveRootSubgroup Γ := by
  ext g
  exact (nativeSubgroupRationalHull_mem_iff (E := E) (I := I) (Γ ⊓ Subgroup.center G) g).trans
    (nativeCenter_original_logSpan_mem_iff_central_roots (I := I) (G := G) Γ g)

end Hindman168
