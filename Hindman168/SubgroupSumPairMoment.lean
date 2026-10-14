import Hindman168.SubgroupHaarComposition
import Hindman168.SubgroupGowersPairTesting

namespace Hindman168
open scoped BigOperators Classical

theorem finiteHaarMean_sup_sum {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (f : G → ℝ) :
    finiteHaarMean (fun n : Q => finiteHaarMean (fun m : R => f ((n : G) + m))) =
      finiteHaarMean (fun z : (Q ⊔ R : AddSubgroup G) => f z) := by
  simpa only [subgroupHaarMean, zero_add] using subgroupHaarMean_sup Q R f 0

theorem finiteHaarMean_sup_pair {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (f : G → G → ℝ) :
    finiteHaarMean (fun a : Q × R => finiteHaarMean (fun b : Q × R =>
      f ((a.1 : G) + a.2) ((b.1 : G) + b.2))) =
        finiteHaarMean (fun z : (Q ⊔ R : AddSubgroup G) =>
          finiteHaarMean (fun z' : (Q ⊔ R : AddSubgroup G) => f z z')) := by
  simp_rw [finiteHaarMean_prod]
  have hb (a : G) := finiteHaarMean_sup_sum Q R (f a)
  simp only [hb]
  exact finiteHaarMean_sup_sum Q R (fun a =>
    finiteHaarMean (fun z : (Q ⊔ R : AddSubgroup G) => f a z))

/-- The genuine next-order moment also holds when both shifts are sampled
independently from the two summand subgroups. -/
theorem weightedSubgroupGowersValue_sum_pair_moment
    {G κ : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (k : ℕ) (hk : 0 < k) (g : κ → G → ℝ) :
    finiteHaarMean (fun a : Q × R => finiteHaarMean (fun b : Q × R =>
      weightedSubgroupGowersValue (Q ⊔ R) p k (fun c x =>
        g c (x + ((a.1 : G) + a.2)) * g c (x + ((b.1 : G) + b.2))) ^ (2 ^ k))) =
      weightedSubgroupGowersValue (Q ⊔ R) p (k + 1) g ^ (2 ^ (k + 1)) := by
  have ht := finiteHaarMean_sup_pair Q R (fun a b : G =>
    weightedSubgroupGowersValue (Q ⊔ R) p k
      (fun c x => g c (x + a) * g c (x + b)) ^ (2 ^ k))
  exact ht.trans (weightedSubgroupGowersValue_pair_moment (Q ⊔ R) p hp k hk g)

/-- A uniform small-test hypothesis and the sum-subgroup moment bound the
absolute paired correlation with the original cell weights. -/
theorem weightedSubgroupGowersValue_sum_pair_test_bound
    {G κ : Type*} [AddCommGroup G] [Fintype G] [Fintype κ]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (k : ℕ) (hk : 0 < k)
    (g : κ → G → ℝ) (r : (Q × R) → (Q × R) → ℝ)
    (hr : ∀ a b, |r a b| ≤ 1) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hsmall : ∀ (a b : Q × R), weightedSubgroupGowersValue (Q ⊔ R) p k
      (fun c x => g c (x + ((a.1 : G) + a.2)) * g c (x + ((b.1 : G) + b.2))) ≤ δ →
        |r a b| ≤ ε) :
    finiteHaarMean (fun a : Q × R => finiteHaarMean (fun b : Q × R => |r a b|)) ≤
      ε + weightedSubgroupGowersValue (Q ⊔ R) p (k + 1) g ^ (2 ^ (k + 1)) / δ ^ (2 ^ k) := by
  have hb (a : Q × R) := finiteHaarMean_abs_le_of_power_threshold
    (fun b : Q × R => weightedSubgroupGowersValue (Q ⊔ R) p k (fun c x =>
      g c (x + ((a.1 : G) + a.2)) * g c (x + ((b.1 : G) + b.2)))) (r a)
    (fun b => weightedSubgroupGowersValue_nonneg (Q ⊔ R) p hp k hk _) (hr a)
    (2 ^ k) ε δ hε hδ (hsmall a)
  calc
    _ ≤ finiteHaarMean (fun a : Q × R => ε + finiteHaarMean (fun b : Q × R =>
        weightedSubgroupGowersValue (Q ⊔ R) p k (fun c x =>
          g c (x + ((a.1 : G) + a.2)) * g c (x + ((b.1 : G) + b.2))) ^ (2 ^ k)) /
            δ ^ (2 ^ k)) := finiteHaarMean_mono _ _ hb
    _ = _ := by
      rw [finiteHaarMean_add, finiteHaarMean_const]
      simp only [div_eq_mul_inv, finiteHaarMean_mul_const]
      rw [weightedSubgroupGowersValue_sum_pair_moment Q R p hp k hk g]

end Hindman168
