import Hindman168.NativeCentralSubspaceSubgroup
import Hindman168.NativeGroupLowerCentralExact

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] [ConnectedSpace G] [SimplyConnectedSpace G]
  [Group.IsNilpotent G] [FiniteDimensional ℝ E] in
theorem nativeLieLowerCentralModel_le_center_of_next_bot (j : ℕ)
    (hj : nativeLieLowerCentralModel (I := I) (G := G) (j+1) = ⊥) :
    nativeLieLowerCentralModel (I := I) (G := G) j ≤ nativeLieCenterModel (I := I) (G := G) := by
  intro v hv
  apply (nativeLieCenterModel_mem_iff_generator_eq_zero (I := I) (G := G) v).mpr
  ext w
  have h := nativeLieAdjointGenerator_mem_lowerCentral_next (I := I) (G := G) w hv
  rw [hj, Submodule.mem_bot] at h
  rw [nativeLieAdjointGenerator_alternating (I := I) (G := G) v w, h, neg_zero]
  rfl

theorem nativeCentralSubspaceSubgroup_le_group_layer (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (j : ℕ)
    (hj : V ≤ nativeLieLowerCentralModel (I := I) (G := G) j) :
    nativeCentralSubspaceSubgroup (I := I) V hV ≤ (⊤ : Subgroup G).lowerCentralSeries j := by
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)]
  rintro g ⟨v, hv, rfl⟩
  exact ⟨v, hj hv, rfl⟩

end Hindman168
