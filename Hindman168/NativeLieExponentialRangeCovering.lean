import Hindman168.NativeLieExponentialPeriods
import Mathlib.Topology.Covering.Quotient

/-! The actual original exponential onto its actual range is a covering
map by the proved original additive period subgroup. The genuine open
surjection onto that range is a quotient map, and actual fiber equality
and original period discreteness instantiate the subgroup covering theorem.
No claim of surjectivity onto the whole original group is made. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieExponentialToRange :
    E → Set.range (nativeLieExponential (I := I) (G := G) : E → G) :=
  Set.rangeFactorization (nativeLieExponential (I := I) (G := G) : E → G)

omit [Group.IsNilpotent G] in
 theorem nativeLieExponentialToRange_surjective :
    Surjective (nativeLieExponentialToRange (I := I) (G := G)) := by
  rintro ⟨g, v, rfl⟩
  exact ⟨v, rfl⟩

omit [Group.IsNilpotent G] in
 theorem nativeLieExponentialToRange_continuous :
    Continuous (nativeLieExponentialToRange (I := I) (G := G)) := by
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  have hc : Continuous exp := (nativeLieExponential_contMDiff (I := I) (G := G)).continuous
  exact hc.codRestrict (s := Set.range exp) (fun v => ⟨v, rfl⟩)

 theorem nativeLieExponentialToRange_isOpenMap :
    IsOpenMap (nativeLieExponentialToRange (I := I) (G := G)) := by
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  have ho : IsOpenMap exp := nativeLieExponential_isOpenMap (I := I) (G := G)
  exact ho.codRestrict (s := Set.range exp) (fun v => ⟨v, rfl⟩)

 theorem nativeLieExponentialToRange_isQuotientMap :
    IsQuotientMap (nativeLieExponentialToRange (I := I) (G := G)) :=
  (nativeLieExponentialToRange_isOpenMap (I := I) (G := G)).isQuotientMap
    nativeLieExponentialToRange_continuous nativeLieExponentialToRange_surjective

 theorem nativeLieExponentialToRange_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (nativeLieExponentialToRange (I := I) (G := G))
      (nativeLieExponentialPeriods (I := I) (G := G)) := by
  apply (nativeLieExponentialToRange_isQuotientMap (I := I) (G := G)).isAddQuotientCoveringMap_of_addSubgroup
    (nativeLieExponentialPeriods (I := I) (G := G)) nativeLieExponentialPeriods_discrete
  intro v w
  constructor
  · intro h
    have he : nativeLieExponential (I := I) (G := G) w =
        nativeLieExponential (I := I) (G := G) v := (congrArg Subtype.val h).symm
    simpa only [sub_eq_add_neg] using (nativeLieExponential_eq_iff_sub_mem_periods w v).mp he
  · intro h
    have hp : w - v ∈ nativeLieExponentialPeriods (I := I) (G := G) := by
      simpa only [sub_eq_add_neg] using h
    exact Subtype.ext ((nativeLieExponential_eq_iff_sub_mem_periods w v).mpr hp).symm

 theorem nativeLieExponentialToRange_isCoveringMap :
    IsCoveringMap (nativeLieExponentialToRange (I := I) (G := G)) :=
  (nativeLieExponentialToRange_isAddQuotientCoveringMap (I := I) (G := G)).isCoveringMap

end Hindman168
