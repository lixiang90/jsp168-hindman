import Hindman168.NativeCentralSubspaceSubgroup

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeCentralSubspace_coset_relation (V : Submodule ℝ E)
    (hV : V ≤ nativeLieCenterModel (I := I) (G := G)) (v w : E) :
    v-w ∈ V ↔ (nativeLieExponential (I := I) (G := G) v)⁻¹ *
      nativeLieExponential (I := I) (G := G) w ∈ nativeCentralSubspaceSubgroup (I := I) V hV := by
  let exp : E → G := fun x => nativeLieExponential (I := I) (G := G) x
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let N := nativeCentralSubspaceSubgroup (I := I) V hV
  change v-w ∈ V ↔ (exp v)⁻¹ * exp w ∈ N
  constructor
  · intro hvw
    have hwv : w-v ∈ V := by simpa only [neg_sub] using V.neg_mem hvw
    have hc : exp (w-v) ∈ Subgroup.center G :=
      (nativeLieExponential_mem_center_iff_mem_centerModel (I := I) (G := G) (w-v)).mpr (hV hwv)
    have he : exp w = exp (w-v)*exp v := by
      simpa only [sub_add_cancel] using
        (nativeLieExponential_add_of_mem_centerModel (I := I) (G := G) (w := v) (hV hwv))
    rw [he, ← Subgroup.mem_center_iff.mp hc (exp v), inv_mul_cancel_left]
    exact ⟨w-v, hwv, rfl⟩
  · intro hc
    let c := (exp v)⁻¹ * exp w
    have hlc : log c ∈ V := (nativeCentralSubspaceSubgroup_mem_logarithm V hV c).mp hc
    have hcC := nativeCentralSubspaceSubgroup_le_center V hV hc
    have hcv : c*exp v = exp w :=
      (Subgroup.mem_center_iff.mp hcC (exp v)).symm.trans (mul_inv_cancel_left (exp v) (exp w))
    have he : exp (log c+v) = exp w :=
      (nativeLieExponential_add_of_mem_centerModel (I := I) (G := G) (w := v) (hV hlc)).trans
        ((congrArg (fun g : G => g*exp v) (nativeLieExponential_globalLogarithm (I := I) c)).trans hcv)
    have hvw : log c+v = w := nativeLieExponential_injective (I := I) (G := G) he
    have hd : v-w = -log c := by rw [← hvw]; abel
    rw [hd]
    exact V.neg_mem hlc

end Hindman168
