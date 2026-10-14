import Hindman168.FiniteHaarCauchySchwarz
import Hindman168.WeightedSubgroupGowersMonotone

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_pow_two_pow_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (n : ℕ) :
    finiteHaarMean f ^ (2 ^ n) ≤ finiteHaarMean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simpa using finiteHaarMean_square_le f
    | succ n =>
      have hn : 0 ≤ finiteHaarMean f ^ (2 ^ (n + 1)) := by
        rw [pow_succ, pow_mul]
        exact sq_nonneg _
      calc
        _ = (finiteHaarMean f ^ (2 ^ (n + 1))) ^ 2 := by rw [pow_succ _ (n + 1), pow_mul]
        _ ≤ (finiteHaarMean (fun x => f x ^ (2 ^ (n + 1)))) ^ 2 := pow_le_pow_left₀ hn ih 2
        _ ≤ finiteHaarMean (fun x => (f x ^ (2 ^ (n + 1))) ^ 2) := finiteHaarMean_square_le _
        _ = _ := by simp only [pow_succ _ (n + 1), pow_mul]

theorem probabilityWeighted_pow_two_pow_le {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) (n : ℕ) :
    (∑ c, p c * f c) ^ (2 ^ n) ≤ ∑ c, p c * f c ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simpa using probabilityWeighted_square_le p f hp hsum
    | succ n =>
      have hn : 0 ≤ (∑ c, p c * f c) ^ (2 ^ (n + 1)) := by
        rw [pow_succ, pow_mul]
        exact sq_nonneg _
      calc
        _ = ((∑ c, p c * f c) ^ (2 ^ (n + 1))) ^ 2 := by rw [pow_succ _ (n + 1), pow_mul]
        _ ≤ (∑ c, p c * f c ^ (2 ^ (n + 1))) ^ 2 := pow_le_pow_left₀ hn ih 2
        _ ≤ ∑ c, p c * (f c ^ (2 ^ (n + 1))) ^ 2 :=
          probabilityWeighted_square_le p _ hp hsum
        _ = _ := by simp only [pow_succ _ (n + 1), pow_mul]

end Hindman168
