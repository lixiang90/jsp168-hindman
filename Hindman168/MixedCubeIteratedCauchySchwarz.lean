import Hindman168.MixedCubeCoordinatePermutation

namespace Hindman168
open scoped BigOperators Classical

noncomputable def cubePartialCopy {G : Type*} (d : ℕ) (S T : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) : Finset (Fin d) → G → ℝ :=
  fun ω => f ((ω \ S) ∪ T)

theorem cubePartialCopy_empty {G : Type*} (d : ℕ) (f : Finset (Fin d) → G → ℝ) :
    cubePartialCopy d ∅ ∅ f = f := by
  funext ω x
  simp [cubePartialCopy]

theorem cubePartialCopy_univ {G : Type*} (d : ℕ) (T : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) :
    cubePartialCopy d Finset.univ T f = fun _ => f T := by
  funext ω x
  have he : ω \ Finset.univ = ∅ := by
    ext k
    simp
  simp only [cubePartialCopy, he, Finset.empty_union]

theorem cubePartialCopy_face {G : Type*} (d : ℕ) (S T : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) (hT : T ⊆ S) (b : Bool)
    (f : Finset (Fin d) → G → ℝ) :
    cubePartialCopy d S T (cubeFaceCopy d i b f) =
      cubePartialCopy d (insert i S) (if b then insert i T else T) f := by
  have hiT : i ∉ T := fun h => hi (hT h)
  funext ω x
  cases b <;> simp only [cubePartialCopy, cubeFaceCopy, Bool.false_eq_true, ↓reduceIte]
  all_goals
    apply congrArg (fun s => f s x)
    ext k
    by_cases hk : k = i <;> simp_all

theorem subgroupMixedCubeAverage_partial_cs {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (S : Finset (Fin d)) (f : Finset (Fin d) → G → ℝ) :
    |subgroupMixedCubeAverage Q d f| ^ (2 ^ S.card) ≤
      ∏ T ∈ S.powerset, |subgroupMixedCubeAverage Q d (cubePartialCopy d S T f)| := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [cubePartialCopy_empty]
  | @insert i S hi ih =>
    have hc := subgroupMixedCubeAverage_reflection_bound_any Q d i f
    have h0 := subgroupMixedCubeAverage_copy_nonneg_any Q d i false f
    have h1 := subgroupMixedCubeAverage_copy_nonneg_any Q d i true f
    have ha : |subgroupMixedCubeAverage Q d f| ^ 2 ≤
        |subgroupMixedCubeAverage Q d (cubeFaceCopy d i false f)| *
        |subgroupMixedCubeAverage Q d (cubeFaceCopy d i true f)| := by
      simpa only [sq_abs, abs_of_nonneg h0, abs_of_nonneg h1] using hc
    rw [Finset.card_insert_of_notMem hi, pow_succ, Nat.mul_comm (2 ^ S.card) 2, pow_mul]
    refine (pow_le_pow_left₀ (sq_nonneg _) ha _).trans ?_
    rw [mul_pow, Finset.prod_powerset_insert hi]
    have hb := mul_le_mul (ih (cubeFaceCopy d i false f)) (ih (cubeFaceCopy d i true f))
      (pow_nonneg (abs_nonneg _) _) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    refine hb.trans_eq ?_
    congr 1
    · apply Finset.prod_congr rfl
      intro T hT
      rw [cubePartialCopy_face d S T i hi (Finset.mem_powerset.mp hT) false f]
      rfl
    · apply Finset.prod_congr rfl
      intro T hT
      rw [cubePartialCopy_face d S T i hi (Finset.mem_powerset.mp hT) true f]
      rfl

theorem subgroupMixedCubeAverage_gowers_cauchy_schwarz {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (f : Finset (Fin d) → G → ℝ) :
    |subgroupMixedCubeAverage Q d f| ^ (2 ^ d) ≤
      ∏ T : Finset (Fin d), subgroupCubeAverage Q d (f T) := by
  have h := subgroupMixedCubeAverage_partial_cs Q d Finset.univ f
  have he (T : Finset (Fin d)) : subgroupMixedCubeAverage Q d (fun _ => f T) =
      subgroupCubeAverage Q d (f T) := rfl
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.powerset_univ,
    cubePartialCopy_univ, he, abs_of_nonneg (subgroupCubeAverage_nonneg Q d hd _)] using h

theorem subgroupMixedCubeAverage_le_product_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (f : Finset (Fin d) → G → ℝ) :
    |subgroupMixedCubeAverage Q d f| ≤ ∏ T : Finset (Fin d), subgroupGowersValue Q d (f T) := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero d (show (2 : ℕ) ≠ 0 by decide))
    (Finset.prod_nonneg (fun T _ => subgroupGowersValue_nonneg Q d hd (f T)))
  rw [← Finset.prod_pow]
  simp only [subgroupGowersValue_pow Q d hd]
  exact subgroupMixedCubeAverage_gowers_cauchy_schwarz Q d hd f

theorem subgroupMixedCubeAverage_le_vertex_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (S : Finset (Fin d)) (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ T, T ≠ S → ∀ x, |f T x| ≤ 1) :
    |subgroupMixedCubeAverage Q d f| ≤ subgroupGowersValue Q d (f S) := by
  refine (subgroupMixedCubeAverage_le_product_gowers Q d hd f).trans ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ S)]
  apply mul_le_of_le_one_right (subgroupGowersValue_nonneg Q d hd (f S))
  exact Finset.prod_le_one (fun T _ => subgroupGowersValue_nonneg Q d hd (f T))
    (fun T hT => subgroupGowersValue_le_one Q d hd (f T) (hf T (Finset.mem_erase.mp hT).1))

end Hindman168
