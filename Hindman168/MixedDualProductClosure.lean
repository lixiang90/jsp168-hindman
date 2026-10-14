import Hindman168.MixedDualRecursion

namespace Hindman168
open scoped BigOperators Classical

theorem subgroupMixedDualFunction_abs_le_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1) (x : G) :
    |subgroupMixedDualFunction Q d f x| ≤ 1 := by
  rw [subgroupMixedDualFunction_eq_vertexDual]
  exact subgroupVertexDual_abs_le_one Q d ∅ f hf x

theorem subgroupMixedDualFunction_correlation_le_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1) (g : G → ℝ) :
    |finiteHaarMean (fun x => g x * subgroupMixedDualFunction Q d f x)| ≤ subgroupGowersValue Q d g := by
  rw [subgroupMixedDualFunction_eq_vertexDual]
  exact subgroupVertexDual_correlation_le_gowers Q d hd ∅ f hf g

theorem subgroupMixedDualFunction_product_average {G ι : Type*}
    [AddCommGroup G] [Fintype ι] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : ι → Finset (Fin d) → G → ℝ) (x : G) :
    (∏ i, subgroupMixedDualFunction Q d (f i) x) =
      finiteHaarMean (fun a : ι → (Fin d → Q) => subgroupMixedDualFunction Q d
        (fun ω y => ∏ i, f i ω (y + ∑ j ∈ ω, (a i j : G))) x) := by
  let H := fun (i : ι) (v : Fin d → Q) =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, f i ω (x + ∑ j ∈ ω, (v j : G))
  have hp (v : Fin d → Q) (a : ι → (Fin d → Q)) :
      (∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        ∏ i, f i ω ((x + ∑ j ∈ ω, (v j : G)) + ∑ j ∈ ω, (a i j : G))) =
        ∏ i, H i (v + a i) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    simp only [H, Pi.add_apply, AddSubgroup.coe_add, Finset.sum_add_distrib, add_assoc]
  unfold subgroupMixedDualFunction
  rw [finiteHaarMean_comm]
  simp_rw [hp]
  have he (v : Fin d → Q) : finiteHaarMean (fun a : ι → (Fin d → Q) => ∏ i, H i (v + a i)) =
      ∏ i, finiteHaarMean (H i) := by
    rw [finiteHaarMean_dependent_pi_prod (fun i a => H i (v + a))]
    simp only [finiteHaarMean_add_left]
  simp only [he, finiteHaarMean_const, H]

theorem subgroupMixedDualFunction_product_correlation_le_gowers {G ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype ι] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (f : ι → Finset (Fin d) → G → ℝ)
    (hf : ∀ i ω, ω ≠ ∅ → ∀ x, |f i ω x| ≤ 1) (g : G → ℝ) :
    |finiteHaarMean (fun x => g x * ∏ i, subgroupMixedDualFunction Q d (f i) x)| ≤
      subgroupGowersValue Q d g := by
  simp_rw [subgroupMixedDualFunction_product_average Q d f, ← finiteHaarMean_const_mul]
  rw [finiteHaarMean_comm]
  refine (finiteHaarMean_abs_mean_le _).trans ?_
  refine (finiteHaarMean_mono _ (fun _ => subgroupGowersValue Q d g) ?_).trans_eq (finiteHaarMean_const _)
  intro a
  apply subgroupMixedDualFunction_correlation_le_gowers Q d hd
  intro ω hω y
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hf i ω hω _)

theorem weighted_mixedDual_product_correlation_le_gowers {G κ ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype ι]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (hd : 0 < d)
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f : κ → ι → Finset (Fin d) → G → ℝ)
    (hf : ∀ c i ω, ω ≠ ∅ → ∀ x, |f c i ω x| ≤ 1) (g : κ → G → ℝ) :
    |∑ c, p c * finiteHaarMean (fun x => g c x * ∏ i, subgroupMixedDualFunction Q d (f c i) x)| ≤
      weightedSubgroupGowersValue Q p d g := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (probabilityWeighted_gowers_le_weightedGowers Q d hd p hp hs g)
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul, abs_of_nonneg (hp c)]
  exact mul_le_mul_of_nonneg_left
    (subgroupMixedDualFunction_product_correlation_le_gowers Q d hd (f c) (hf c) (g c)) (hp c)

end Hindman168
