import Hindman168.NativeSubgroupRationalHullRoots
import Hindman168.NativeCenterRootSpan
import Hindman168.NativeSubgroupRationalNormalizedSpan

/-! The actual central kernel of the ORIGINAL subgroup's rational
logarithmic span is precisely the rational logarithmic span of its
actual center intersection. Full positive-root membership and genuine
central denominator clearing prove the previously missing reverse
inclusion. No lattice or discreteness hypothesis is needed here. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupRationalLogSpan_center_intersection_le (Γ : Subgroup G) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G) ≤
      (nativeLieCenterModel (I := I) (G := G)).restrictScalars ℚ := by
  apply nativeSubgroupRationalLogSpan_le_of_logarithms_mem
  intro g hg
  exact (nativeLieGlobalLogarithm_mem_centerModel_iff (I := I) (G := G) g).mpr hg.2

 theorem nativeSubgroupRationalLogSpan_central_mem_intersection (Γ : Subgroup G)
    {v : E} (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hc : v ∈ nativeLieCenterModel (I := I) (G := G)) :
    v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G) := by
  have hp := (nativeSubgroupRationalLogSpan_mem_iff_positive_power Γ v).mp hv
  have he := (nativeLieExponential_mem_center_iff_mem_centerModel (I := I) (G := G) v).mpr hc
  have hz : nativeLieExponential (I := I) (G := G) v ∈ centralPositiveRootSubgroup Γ :=
    ⟨hp, he⟩
  have hl := (nativeCenter_original_logSpan_mem_iff_central_roots (E := E) (I := I)
    Γ (nativeLieExponential (I := I) (G := G) v)).mpr hz
  simpa only [nativeLieGlobalLogarithm_exponential] using hl

 theorem nativeSubgroupRationalLogSpan_center_kernel_eq (Γ : Subgroup G) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ⊓
        (nativeLieCenterModel (I := I) (G := G)).restrictScalars ℚ =
      nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ ⊓ Subgroup.center G) := by
  apply le_antisymm
  · intro v hv
    exact nativeSubgroupRationalLogSpan_central_mem_intersection Γ hv.1 hv.2
  · exact le_inf (nativeSubgroupRationalLogSpan_mono inf_le_left)
      (nativeSubgroupRationalLogSpan_center_intersection_le Γ)

 theorem nativeSubgroupRationalHull_center_intersection_eq (Γ : Subgroup G) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ ⊓ Subgroup.center G =
      nativeSubgroupRationalHull (E := E) (I := I) (Γ ⊓ Subgroup.center G) := by
  rw [nativeCenter_intersection_rationalHull_eq_positiveRoots,
    nativeSubgroupRationalHull_eq_positiveRoots]
  ext g
  exact Iff.rfl

end Hindman168
