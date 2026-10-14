import Hindman168.NativeLieCenterExponential
import Mathlib.Topology.Algebra.Group.Quotient

namespace Hindman168
open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeCentralSubspaceSubgroup (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) : Subgroup G where
  carrier := (fun v : E => nativeLieExponential (I := I) (G := G) v) '' (V : Set E)
  one_mem' := ⟨0, V.zero_mem, nativeLieExponential_zero (I := I) (G := G)⟩
  mul_mem' := by
    rintro a b ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v+w, V.add_mem hv hw, nativeLieExponential_add_of_mem_centerModel (hV hv)⟩
  inv_mem' := by
    rintro a ⟨v, hv, rfl⟩
    exact ⟨-v, V.neg_mem hv, nativeLieExponential_neg (I := I) (G := G) v⟩

theorem nativeCentralSubspaceSubgroup_mem_logarithm (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (g : G) :
    g ∈ nativeCentralSubspaceSubgroup (I := I) V hV ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [nativeLieGlobalLogarithm_exponential]
  · intro hg
    exact ⟨nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g, hg,
      nativeLieExponential_globalLogarithm (I := I) g⟩

theorem nativeCentralSubspaceSubgroup_le_center (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    nativeCentralSubspaceSubgroup (I := I) V hV ≤ Subgroup.center G := by
  rintro g ⟨v, hv, rfl⟩
  exact (nativeLieExponential_mem_center_iff_mem_centerModel v).mpr (hV hv)

theorem nativeCentralSubspaceSubgroup_normal (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    (nativeCentralSubspaceSubgroup (I := I) V hV).Normal := by
  refine ⟨?_⟩
  intro a ha g
  have hc := nativeCentralSubspaceSubgroup_le_center V hV ha
  simpa only [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right] using ha

theorem nativeCentralSubspaceSubgroup_closed (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) :
    IsClosed (nativeCentralSubspaceSubgroup (I := I) V hV : Set G) := by
  have he : (nativeCentralSubspaceSubgroup (I := I) V hV : Set G) =
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ⁻¹' (V : Set E) :=
    Set.ext (nativeCentralSubspaceSubgroup_mem_logarithm V hV)
  rw [he]
  exact V.closed_of_finiteDimensional.preimage
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous

theorem nativeCentralSubspaceSubgroup_exponential_mem_iff (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (v : E) :
    nativeLieExponential (I := I) (G := G) v ∈ nativeCentralSubspaceSubgroup (I := I) V hV ↔ v ∈ V := by
  rw [nativeCentralSubspaceSubgroup_mem_logarithm, nativeLieGlobalLogarithm_exponential]

end Hindman168
