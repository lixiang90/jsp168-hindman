import Hindman168.SubgroupGowersDimensionMonotone

namespace Hindman168
open scoped BigOperators

theorem probabilityWeighted_square_le {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) :
    (∑ c, p c * f c) ^ 2 ≤ ∑ c, p c * f c ^ 2 := by
  let m := ∑ c, p c * f c
  have hn : 0 ≤ ∑ c, p c * (f c - m) ^ 2 :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (hp c) (sq_nonneg _))
  have he (c : ι) : p c * (f c - m) ^ 2 =
      p c * f c ^ 2 - (p c * f c) * (2 * m) + p c * m ^ 2 := by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum, one_mul] at hn
  change 0 ≤ (∑ c, p c * f c ^ 2) - m * (2 * m) + m ^ 2 at hn
  change m ^ 2 ≤ _
  nlinarith

variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedSubgroupCubeAverage_square_le_succ {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d : ℕ) (h : ι → G → ℝ) :
    weightedSubgroupCubeAverage p Q d h ^ 2 ≤
      weightedSubgroupCubeAverage p Q (d + 1) h := by
  exact (probabilityWeighted_square_le p (fun c => subgroupCubeAverage Q d (h c)) hp hsum).trans
    (Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
      (subgroupCubeAverage_square_le_succ Q d (h c)) (hp c)))

theorem weightedSubgroupGowersValue_le_succ {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d : ℕ) (hd : 0 < d) (h : ι → G → ℝ) :
    weightedSubgroupGowersValue Q p d h ≤ weightedSubgroupGowersValue Q p (d + 1) h := by
  have hpow (e : ℕ) (he : 0 < e) : weightedSubgroupGowersValue Q p e h ^ (2 ^ e) =
      weightedSubgroupCubeAverage p Q e h := by
    rw [weightedSubgroupGowersValue_pow Q p hp e he]
    simp only [subgroupGowersValue_pow Q e he, weightedSubgroupCubeAverage]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero (d + 1) (show (2 : ℕ) ≠ 0 by decide))
    (weightedSubgroupGowersValue_nonneg Q p hp (d + 1) (by omega) h)
  rw [hpow (d + 1) (by omega), pow_succ, pow_mul, hpow d hd]
  exact weightedSubgroupCubeAverage_square_le_succ Q p hp hsum d h

theorem weightedSubgroupGowersValue_dimension_mono {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (d e : ℕ) (hd : 0 < d) (hde : d ≤ e) (h : ι → G → ℝ) :
    weightedSubgroupGowersValue Q p d h ≤ weightedSubgroupGowersValue Q p e h := by
  induction e, hde using Nat.le_induction with
  | base => exact le_rfl
  | succ e hde ih =>
    exact ih.trans
      (weightedSubgroupGowersValue_le_succ Q p hp hsum e (lt_of_lt_of_le hd hde) h)

end Hindman168
