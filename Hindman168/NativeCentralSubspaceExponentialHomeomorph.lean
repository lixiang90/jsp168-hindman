import Hindman168.NativeCentralSubspaceSubgroup

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceExponentialHomeomorph (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    V ≃ₜ nativeCentralSubspaceSubgroup (I := I) V hV where
  toFun v := ⟨nativeLieExponential (I := I) (G := G) v.val, ⟨v.val, v.property, rfl⟩⟩
  invFun g := ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val,
    (nativeCentralSubspaceSubgroup_mem_logarithm V hV g.val).mp g.property⟩
  left_inv v := Subtype.ext (nativeLieGlobalLogarithm_exponential (I := I) (G := G) v.val)
  right_inv g := Subtype.ext (nativeLieExponential_globalLogarithm (I := I) (G := G) g.val)
  continuous_toFun :=
    ((nativeLieExponential_contMDiff (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous.comp continuous_subtype_val).subtype_mk _

end Hindman168
