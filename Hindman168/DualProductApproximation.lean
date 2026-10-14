import Hindman168.SubgroupMixedCubeDuality
import Mathlib.Algebra.Order.Chebyshev

namespace Hindman168
open scoped BigOperators Classical

theorem unit_product_squared_difference_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hg : ∀ i ∈ S, |g i| ≤ 1) :
    ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) ^ 2 ≤
      (S.card : ℝ) * ∑ i ∈ S, (f i - g i) ^ 2 := by
  have h := unit_product_difference_le S f g hf hg
  have hb := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |f i - g i|)
  have hn := abs_nonneg ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)
  have he := sq_abs ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)
  simp only [sq_abs] at hb
  nlinarith

theorem weightedHaar_product_L2_stability {ι X κ : Type*}
    [Fintype X] [Fintype κ] (S : Finset ι) (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c)
    (f g : ι → κ → X → ℝ)
    (hf : ∀ i ∈ S, ∀ c x, |f i c x| ≤ 1) (hg : ∀ i ∈ S, ∀ c x, |g i c x| ≤ 1) :
    (∑ c, p c * finiteHaarMean (fun x => ((∏ i ∈ S, f i c x) - ∏ i ∈ S, g i c x) ^ 2)) ≤
      (S.card : ℝ) * ∑ i ∈ S, ∑ c, p c * finiteHaarMean (fun x => (f i c x - g i c x) ^ 2) := by
  calc
    _ ≤ ∑ c, p c * finiteHaarMean (fun x => (S.card : ℝ) * ∑ i ∈ S, (f i c x - g i c x) ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hp c)
      apply finiteHaarMean_mono
      intro x
      exact unit_product_squared_difference_le S _ _ (fun i hi => hf i hi c x) (fun i hi => hg i hi c x)
    _ = _ := by
      simp only [finiteHaarMean_const_mul, finiteHaarMean_finset_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem weighted_dual_product_exists_approximation {G κ ι : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] [Fintype ι]
    (Q : ι → AddSubgroup G) (d : ℕ) (p : κ → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f : ι → κ → G → ℝ) (hf : ∀ i c x, |f i c x| ≤ 1) (m : ℕ) (hm : 0 < m) :
    ∃ s : (i : ι) → Fin m → (Fin d → Q i),
      let a := fun (c : κ) (x : G) => ∏ i, ((∑ j,
        ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
          f i c (x + ∑ k ∈ ω, (s i j k : G))) / m)
      let D := fun c x => ∏ i, subgroupDualFunction (Q i) d (f i c) x
      (∀ c x, |a c x| ≤ 1) ∧
      (∑ c, p c * finiteHaarMean (fun x => (a c x - D c x) ^ 2)) ≤
        (Fintype.card ι : ℝ) ^ 2 / m ∧
      ∀ g : κ → G → ℝ, (∀ c x, |g c x| ≤ 1) →
        (∑ c, p c * finiteHaarMean (fun x => g c x * (a c x - D c x))) ^ 2 ≤
          (Fintype.card ι : ℝ) ^ 2 / m := by
  have hex (i : ι) := weighted_subgroupDualFunction_exists_approximation
    (Q i) d p hp hs (f i) (hf i) m hm
  choose s hb he ht using hex
  let A := fun (i : ι) (c : κ) (x : G) => ((∑ j,
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      f i c (x + ∑ k ∈ ω, (s i j k : G))) / m)
  have hA (i : ι) (c : κ) (x : G) : |A i c x| ≤ 1 := hb i c x
  have hL : (∑ c, p c * finiteHaarMean (fun x =>
      ((∏ i, A i c x) - ∏ i, subgroupDualFunction (Q i) d (f i c) x) ^ 2)) ≤
      (Fintype.card ι : ℝ) ^ 2 / m := by
    refine (weightedHaar_product_L2_stability Finset.univ p hp A
      (fun i c => subgroupDualFunction (Q i) d (f i c))
      (fun i _ => hA i) (fun i _ c => subgroupDualFunction_abs_le_one (Q i) d (f i c) (hf i c))).trans ?_
    calc
      _ ≤ (Fintype.card ι : ℝ) * ∑ _i : ι, (1 / (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine ⟨s, ?_, hL, ?_⟩
  · intro c x
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hA i c x)
  · intro g hg
    exact (weightedHaar_discard_unit_factor p hp hs g _ hg).trans hL

end Hindman168
