import Hindman168.NativeSubgroupBracketSpan
import Hindman168.RationalBilinearRealSpan
import Hindman168.NativeLieSubalgebraTopology

/-! The actual real span of the actual logarithms of a specified original
subgroup is an original native Lie subalgebra. Its genuine exponential
image is a closed contractible subgroup containing that specified subgroup.
No cocompactness or equality with the whole group is assumed. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupRationalLogSpan_real_span_eq (Γ : Subgroup G) :
    span ℝ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Set E) =
      span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G)) := by
  let S : Submodule ℝ E :=
    span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G))
  apply le_antisymm
  · apply span_le.mpr
    have hle : nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ≤ S.restrictScalars ℚ := by
      apply span_le.mpr
      intro v hv
      exact subset_span hv
    exact hle
  · apply span_mono
    exact subset_span

noncomputable def nativeSubgroupRealLieSpan (Γ : Subgroup G) :
    LieSubalgebra ℝ (GroupLieAlgebra I G) where
  toSubmodule := span ℝ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Set E)
  lie_mem' := by
    intro x y hx hy
    have hB := rationalBilinear_realSpan_mem
      (nativeLieAdjointDifferential (I := I) (G := G))
      (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
      (fun _ hv _ hw => nativeSubgroupRationalLogSpan_differential_mem Γ hv hw) hx hy
    have he : nativeLieAdjointDifferential (I := I) (G := G) x y = (⁅x, y⁆ : GroupLieAlgebra I G) := by
      rw [← nativeLieAdjointGenerator_eq_differential]
      exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y
    exact he ▸ hB

 theorem nativeSubgroupRealLieSpan_model_eq (Γ : Subgroup G) :
    nativeLieSubalgebraModel (E := E) (nativeSubgroupRealLieSpan (E := E) (I := I) Γ) =
      span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) '' (Γ : Set G)) :=
  nativeSubgroupRationalLogSpan_real_span_eq (E := E) (I := I) Γ

 theorem nativeSubgroup_le_realLieSpan_subgroup (Γ : Subgroup G) :
    Γ ≤ nativeLieSubalgebraSubgroup (E := E) (nativeSubgroupRealLieSpan (E := E) (I := I) Γ) := by
  intro g hg
  apply (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) _ g).mpr
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
    span ℝ (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ : Set E)
  exact subset_span (nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg)

 theorem nativeSubgroupRealLieSpan_subgroup_closed (Γ : Subgroup G) :
    IsClosed (nativeLieSubalgebraSubgroup (E := E)
      (nativeSubgroupRealLieSpan (E := E) (I := I) Γ) : Set G) :=
  nativeLieSubalgebraSubgroup_closed _

 theorem nativeSubgroupRealLieSpan_subgroup_contractible (Γ : Subgroup G) :
    ContractibleSpace (nativeLieSubalgebraSubgroup (E := E)
      (nativeSubgroupRealLieSpan (E := E) (I := I) Γ)) :=
  nativeLieSubalgebraSubgroup_contractible _

end Hindman168
