import Hindman168.NativeLieCenterExponential

/-! Exact original center coset equivalence in the actual exponential
coordinates. Two original vectors represent the same original group
center coset precisely when their difference lies in the actual real
adjoint kernel, proved from central exponential addition and injectivity. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieCenter_coset_relation (v w : E) :
    v - w ∈ nativeLieCenterModel (I := I) (G := G) ↔
      (nativeLieExponential (I := I) (G := G) v)⁻¹ *
        nativeLieExponential (I := I) (G := G) w ∈ Subgroup.center G := by
  let V : Submodule ℝ E := nativeLieCenterModel (I := I) (G := G)
  let exp : E → G := fun x => nativeLieExponential (I := I) (G := G) x
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  change v - w ∈ V ↔ (exp v)⁻¹ * exp w ∈ Subgroup.center G
  constructor
  · intro hvw
    have hwv : w - v ∈ V := by simpa only [neg_sub] using V.neg_mem hvw
    have hc : exp (w - v) ∈ Subgroup.center G :=
      (nativeLieExponential_mem_center_iff_mem_centerModel (I := I) (G := G) (w - v)).mpr hwv
    have he : exp w = exp (w - v) * exp v := by
      simpa only [sub_add_cancel] using
        (nativeLieExponential_add_of_mem_centerModel (I := I) (G := G) (w := v) hwv)
    rw [he, ← Subgroup.mem_center_iff.mp hc (exp v), inv_mul_cancel_left]
    exact hc
  · intro hc
    let c : G := (exp v)⁻¹ * exp w
    have hlc : log c ∈ V :=
      (nativeLieGlobalLogarithm_mem_centerModel_iff (E := E) (I := I) (G := G) c).mpr hc
    have hcv : c * exp v = exp w :=
      (Subgroup.mem_center_iff.mp hc (exp v)).symm.trans (mul_inv_cancel_left (exp v) (exp w))
    have he : exp (log c + v) = exp w :=
      (nativeLieExponential_add_of_mem_centerModel (I := I) (G := G) (w := v) hlc).trans
        ((congrArg (fun g : G => g * exp v)
          (nativeLieExponential_globalLogarithm (E := E) (I := I) c)).trans hcv)
    have hvw : log c + v = w := nativeLieExponential_injective (E := E) (I := I) (G := G) he
    have hd : v - w = -log c := by rw [← hvw]; abel
    rw [hd]
    exact V.neg_mem hlc

theorem nativeLieCenter_quotient_exponential_eq_iff (v w : E) :
    (QuotientGroup.mk (nativeLieExponential (I := I) (G := G) v) : G ⧸ Subgroup.center G) =
      QuotientGroup.mk (nativeLieExponential (I := I) (G := G) w) ↔
        v - w ∈ nativeLieCenterModel (I := I) (G := G) :=
  QuotientGroup.eq.trans (nativeLieCenter_coset_relation (I := I) (G := G) v w).symm

end Hindman168
