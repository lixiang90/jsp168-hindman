import Hindman168.SubgroupDualRecursion
import Hindman168.HaarMeanTestError

namespace Hindman168
open scoped BigOperators Classical

theorem unit_product_difference_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hg : ∀ i ∈ S, |g i| ≤ 1) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, |f i - g i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hfs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : |∏ i ∈ S, f i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hfs
    have he : f a * (∏ i ∈ S, f i) - g a * (∏ i ∈ S, g i) =
        (f a - g a) * (∏ i ∈ S, f i) + g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) := by ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hprod)
      ((mul_le_of_le_one_left (abs_nonneg _) (hg a (Finset.mem_insert_self a S))).trans (ih hfs hgs))

theorem finiteHaarMean_abs_mean_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |finiteHaarMean f| ≤ finiteHaarMean (fun i => |f i|) := by
  rw [finiteHaarMean, finiteHaarMean, abs_div, abs_of_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem finiteHaarMean_finset_sum {ι α : Type*} [Fintype α] (S : Finset ι) (f : ι → α → ℝ) :
    finiteHaarMean (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, finiteHaarMean (f i) := by
  simp only [finiteHaarMean, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem subgroupDualFunction_difference_bound {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f g : G → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) (x : G) :
    |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x| ≤
      finiteHaarMean (fun v : Fin d → Q =>
        ∑ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
          |f (x + ∑ j ∈ ω, (v j : G)) - g (x + ∑ j ∈ ω, (v j : G))|) := by
  unfold subgroupDualFunction
  rw [← finiteHaarMean_sub]
  refine (finiteHaarMean_abs_mean_le _).trans (finiteHaarMean_mono _ _ ?_)
  intro v
  exact unit_product_difference_le _ _ _ (fun _ _ => hf _) (fun _ _ => hg _)

theorem subgroupDualFunction_L1_stability {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f g : G → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    finiteHaarMean (fun x => |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x|) ≤
      (2 ^ d - 1 : ℕ) * finiteHaarMean (fun x => |f x - g x|) := by
  refine (finiteHaarMean_mono _ _ (subgroupDualFunction_difference_bound Q d f g hf hg)).trans_eq ?_
  rw [finiteHaarMean_comm]
  simp_rw [finiteHaarMean_finset_sum]
  have ht (a : G) : finiteHaarMean (fun x => |f (x + a) - g (x + a)|) =
      finiteHaarMean (fun x => |f x - g x|) :=
    finiteHaarMean_equiv (Equiv.addRight a) (fun x => |f x - g x|)
  simp_rw [ht]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ ∅),
    Finset.card_univ, Fintype.card_finset, Fintype.card_fin, finiteHaarMean_const]

theorem subgroupDualFunction_L2_square_stability {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f g : G → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    finiteHaarMean (fun x => (subgroupDualFunction Q d f x - subgroupDualFunction Q d g x) ^ 2) ≤
      2 * (2 ^ d - 1 : ℕ) * finiteHaarMean (fun x => |f x - g x|) := by
  have hb (x : G) : |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x| ≤ 2 :=
    by
      have ht := abs_sub_le (subgroupDualFunction Q d f x) 0 (subgroupDualFunction Q d g x)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      have h1 := subgroupDualFunction_abs_le_one Q d f hf x
      have h2 := subgroupDualFunction_abs_le_one Q d g hg x
      linarith
  have hpoint (x : G) : (subgroupDualFunction Q d f x - subgroupDualFunction Q d g x) ^ 2 ≤
      2 * |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x| := by
    have he := sq_abs (subgroupDualFunction Q d f x - subgroupDualFunction Q d g x)
    have hn := abs_nonneg (subgroupDualFunction Q d f x - subgroupDualFunction Q d g x)
    have hx := hb x
    nlinarith
  calc
    _ ≤ finiteHaarMean (fun x => 2 * |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x|) :=
      finiteHaarMean_mono _ _ hpoint
    _ = 2 * finiteHaarMean (fun x => |subgroupDualFunction Q d f x - subgroupDualFunction Q d g x|) :=
      finiteHaarMean_const_mul _ _
    _ ≤ 2 * ((2 ^ d - 1 : ℕ) * finiteHaarMean (fun x => |f x - g x|)) :=
      mul_le_mul_of_nonneg_left (subgroupDualFunction_L1_stability Q d f g hf hg) (by norm_num)
    _ = _ := by ring

end Hindman168
