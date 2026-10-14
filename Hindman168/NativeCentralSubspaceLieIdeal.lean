import Hindman168.NativeCentralSubspaceSubgroup
import Hindman168.NativeLieIdealSubgroup

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceLieIdeal (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) : LieIdeal ℝ (GroupLieAlgebra I G) where
  __ := V
  lie_mem := by
    intro x y hy
    have he := (nativeLieCenterModel_mem_iff_native_bracket_zero (I := I) (G := G) y).mp (hV hy) x
    have hz : ⁅x, y⁆ = 0 := by
      have h := lie_skew x y
      rw [he, neg_zero] at h
      exact h.symm
    exact hz.symm ▸ V.zero_mem

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeCentralSubspaceLieIdeal_model (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    nativeLieSubalgebraModel (E := E) (nativeCentralSubspaceLieIdeal (I := I) V hV).toLieSubalgebra = V := rfl

omit [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeCentralSubspaceLieIdeal_subgroup (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    nativeLieSubalgebraSubgroup (E := E) (nativeCentralSubspaceLieIdeal (I := I) V hV).toLieSubalgebra =
      nativeCentralSubspaceSubgroup (I := I) V hV := by
  ext g
  rfl

end Hindman168
