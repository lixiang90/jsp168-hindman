import Hindman168.NativeLieRationalPairIdealBCH

/-! Actual exponentials of vectors differing in a specified rational
ideal differ by an actual element of its exponential image. This uses
the original pair-ideal BCH theorem, without assuming quotient Exp/Log
maps or normality of the containing group subgroup. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieGlobalLogarithm_ideal_difference
    (V N : Submodule ℚ E) (hNV : N ≤ V)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, nativeLieAdjointDifferential (I := I) (G := G) v n ∈ N)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V) (huw : u - w ∈ N) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * (nativeLieExponential (I := I) (G := G) w)⁻¹) ∈ N := by
  have hb : nativeLieAdjointDifferential (I := I) (G := G) u (-w) ∈ N := by
    have he : nativeLieAdjointDifferential (I := I) (G := G) u (-w) =
        nativeLieAdjointDifferential (I := I) (G := G) w (u - w) := by
      simp only [map_neg, map_sub, nativeLieAdjointDifferential_self, sub_zero]
      rw [nativeLieAdjointDifferential_skew]
      simp only [neg_neg]
    rw [he]
    exact hideal w hw _ huw
  have hp := nativeLieGlobalLogarithm_product_pair_ideal V N hNV hideal hu (V.neg_mem hw) hb
  have hm := N.add_mem hp huw
  rw [← nativeLieExponential_neg (I := I) (G := G) w]
  convert hm using 1
  abel

 theorem nativeLieExponential_mem_of_ideal_difference
    (V N : Submodule ℚ E) (hNV : N ≤ V)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, nativeLieAdjointDifferential (I := I) (G := G) v n ∈ N)
    (K : Subgroup G) (hNK : ∀ n ∈ N, nativeLieExponential (I := I) (G := G) n ∈ K)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V) (huw : u - w ∈ N)
    (huK : nativeLieExponential (I := I) (G := G) u ∈ K) :
    nativeLieExponential (I := I) (G := G) w ∈ K := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have hl := nativeLieGlobalLogarithm_ideal_difference V N hNV hideal hu hw huw
  have hr := hNK _ hl
  rw [nativeLieExponential_globalLogarithm] at hr
  have hm := K.mul_mem (K.inv_mem hr) huK
  change (exp u * (exp w)⁻¹)⁻¹ * exp u ∈ K at hm
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hm

end Hindman168
