import Hindman168.NativeLieCommutatorDerivative

/-! Actual nested commutators in the original group. Their original lower
central membership and actual derivatives prove operator-difference
products vanish when the original group lower central series terminates. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 def nativeGroupCommutatorWord : List G → G → G
  | [], x => x
  | g :: gs, x => nativeGroupCommutatorMap g (nativeGroupCommutatorWord gs x)

omit [TopologicalSpace G] in
 theorem nativeGroupCommutatorWord_one (gs : List G) :
    nativeGroupCommutatorWord gs 1 = 1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [nativeGroupCommutatorWord, ih, nativeGroupCommutatorMap_one]

 theorem nativeGroupCommutatorWord_contMDiff (gs : List G) :
    ContMDiff I I ∞ (nativeGroupCommutatorWord gs) := by
  induction gs with
  | nil => exact contMDiff_id
  | cons g gs ih => exact (nativeGroupCommutatorMap_contMDiff (I := I) g).comp ih

omit [TopologicalSpace G] in
 theorem nativeGroupCommutatorWord_mem_lowerCentral (gs : List G) (x : G) :
    nativeGroupCommutatorWord gs x ∈ (⊤ : Subgroup G).lowerCentralSeries gs.length := by
  induction gs with
  | nil => exact Subgroup.mem_top x
  | cons g gs ih =>
    rw [List.length_cons, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) ih

omit [TopologicalSpace G] in
 theorem nativeGroupCommutatorWord_eq_one_of_lowerCentral_bot {k : ℕ}
    (hk : (⊤ : Subgroup G).lowerCentralSeries k = ⊥) (gs : List G)
    (hlen : gs.length = k) (x : G) : nativeGroupCommutatorWord gs x = 1 := by
  have h := nativeGroupCommutatorWord_mem_lowerCentral gs x
  rw [hlen, hk, Subgroup.mem_bot] at h
  exact h

 theorem nativeGroupCommutatorWord_mfderiv (gs : List G) :
    mfderiv I I (nativeGroupCommutatorWord gs) (1 : G) =
      (gs.map (fun g => nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E)).prod := by
  induction gs with
  | nil =>
    change mfderiv I I (id : G → G) (1 : G) = (1 : E →L[ℝ] E)
    rw [mfderiv_id]
    rfl
  | cons g gs ih =>
    let C : E →L[ℝ] E := mfderiv I I (nativeGroupCommutatorWord (g :: gs)) (1 : G)
    change C = (nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E) *
      (gs.map (fun h => nativeLieAdjoint (I := I) h - ContinuousLinearMap.id ℝ E)).prod
    apply ContinuousLinearMap.ext
    intro v
    have hd := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I) (1 : G)
      ((nativeGroupCommutatorMap_contMDiff (I := I) g).mdifferentiableAt (by norm_num))
      ((nativeGroupCommutatorWord_contMDiff (I := I) gs).mdifferentiableAt (by norm_num))
      (nativeGroupCommutatorWord_one gs) v
    erw [nativeGroupCommutatorMap_mfderiv, ih] at hd
    exact hd

 theorem nativeLieAdjointDifference_products_zero_of_lowerCentral_bot {k : ℕ}
    (hk : (⊤ : Subgroup G).lowerCentralSeries k = ⊥) (gs : List G)
    (hlen : gs.length = k) :
    (gs.map (fun g => nativeLieAdjoint (I := I) g - ContinuousLinearMap.id ℝ E)).prod = 0 := by
  rw [← nativeGroupCommutatorWord_mfderiv]
  have he : nativeGroupCommutatorWord gs = (fun _ : G => (1 : G)) :=
    funext (nativeGroupCommutatorWord_eq_one_of_lowerCentral_bot hk gs hlen)
  rw [he, mfderiv_const]
  rfl

end Hindman168
