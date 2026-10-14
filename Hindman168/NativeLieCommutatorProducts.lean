import Hindman168.NativeLieCommutatorWords
import Hindman168.NativeLieNilpotentAdjoint

/-! Differentiate the proved products of actual adjoint differences along
the original one-parameter curves. Original group lower-central termination
therefore forces products of actual native bracket generators to vanish. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_products_zero_of_lowerCentral_bot {k : ℕ}
    (hk : (⊤ : Subgroup G).lowerCentralSeries k = ⊥) (vs : List E) (hlen : vs.length = k) :
    (vs.map (nativeLieAdjointGenerator (I := I) (G := G))).prod = 0 := by
  let D : G → E →L[ℝ] E := fun g => nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E
  let B := nativeLieAdjointGenerator (I := I) (G := G)
  have ha : ∀ ws : List E, ∀ gs : List G, gs.length + ws.length = k →
      (gs.map D).prod * (ws.map B).prod = 0 := by
    intro ws
    induction ws with
    | nil =>
      intro gs hgs
      have hglen : gs.length = k := by simpa using hgs
      simpa only [List.map_nil, List.prod_nil, mul_one] using
        nativeLieAdjointDifference_products_zero_of_lowerCentral_bot (I := I) hk gs hglen
    | cons v ws ih =>
      intro gs hgs
      have hd := ((nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G) v).sub_const
        (ContinuousLinearMap.id ℝ E)).const_mul (gs.map D).prod
      have ht := hd.mul_const (ws.map B).prod
      have he : (fun t : ℝ => (gs.map D).prod *
          (nativeLieAdjointCurve (I := I) (G := G) v t - ContinuousLinearMap.id ℝ E) *
            (ws.map B).prod) = (fun _ => 0) := by
        funext t
        have hl : (gs ++ [lieOneParameterCurve (I := I) (G := G) v t]).length + ws.length = k := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hgs ⊢
          omega
        have h := ih (gs ++ [lieOneParameterCurve (I := I) (G := G) v t]) hl
        simpa only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          D, nativeLieAdjointCurve] using h
      rw [he] at ht
      have h := ht.unique (hasDerivAt_const (0 : ℝ) (0 : E →L[ℝ] E))
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using h
  have h := ha vs [] (by simpa using hlen)
  simpa only [List.map_nil, List.prod_nil, one_mul] using h

 theorem nativeLieAdjointGenerator_pow_zero_of_lowerCentral_bot {k : ℕ}
    (hk : (⊤ : Subgroup G).lowerCentralSeries k = ⊥) (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v ^ k = 0 := by
  have h := nativeLieAdjointGenerator_products_zero_of_lowerCentral_bot (I := I) hk
    (List.replicate k v) (List.length_replicate ..)
  simpa only [List.map_replicate, List.prod_replicate] using h

end Hindman168
