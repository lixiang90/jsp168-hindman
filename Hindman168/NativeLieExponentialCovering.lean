import Hindman168.NativeLieExponentialSurjective
import Hindman168.NativeLieExponentialRangeCovering

/-! Genuine covering of the whole original connected nilpotent Lie
group. True Picard product logarithms and connectedness prove actual
surjectivity; the original open exponential and actual period fibers
therefore give the whole-group additive-period quotient covering. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_isQuotientMap :
    IsQuotientMap (fun v : E => nativeLieExponential (I := I) (G := G) v) :=
  (nativeLieExponential_isOpenMap (I := I) (G := G)).isQuotientMap
    (nativeLieExponential_contMDiff (I := I) (G := G)).continuous
    (nativeLieExponential_surjective (I := I) (G := G))

 theorem nativeLieExponential_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (fun v : E => nativeLieExponential (I := I) (G := G) v)
      (nativeLieExponentialPeriods (E := E) (I := I) (G := G)) := by
  apply (nativeLieExponential_isQuotientMap (I := I) (G := G)).isAddQuotientCoveringMap_of_addSubgroup
    (nativeLieExponentialPeriods (E := E) (I := I) (G := G))
      (nativeLieExponentialPeriods_discrete (E := E) (I := I) (G := G))
  intro v w
  constructor
  · intro h
    simpa only [sub_eq_add_neg] using
      (nativeLieExponential_eq_iff_sub_mem_periods w v).mp h.symm
  · intro h
    have hp : w - v ∈ nativeLieExponentialPeriods (E := E) (I := I) (G := G) := by
      simpa only [sub_eq_add_neg] using h
    exact ((nativeLieExponential_eq_iff_sub_mem_periods w v).mpr hp).symm

 theorem nativeLieExponential_isCoveringMap :
    IsCoveringMap (fun v : E => nativeLieExponential (I := I) (G := G) v) :=
  (nativeLieExponential_isAddQuotientCoveringMap (I := I) (G := G)).isCoveringMap

end Hindman168
