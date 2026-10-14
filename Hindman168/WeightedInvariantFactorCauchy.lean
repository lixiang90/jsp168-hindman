import Hindman168.SubgroupInvariantFactorCauchy
import Hindman168.WeightedSubgroupGowersMonotone

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weighted_subgroup_invariant_factor_cauchy {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (f g : ι → G → ℝ) (C : ℝ) (hf : ∀ c x, |f c x| ≤ C)
    (hinv : ∀ c x (a : Q), f c (x + a) = f c x) :
    (∑ c, p c * finiteHaarMean (fun x => f c x * g c x)) ^ 2 ≤
      C ^ 2 * ∑ c, p c * finiteHaarMean
        (fun x => finiteHaarMean (fun a : Q => g c x * g c (x + a))) := by
  calc
    _ ≤ ∑ c, p c * (finiteHaarMean (fun x => f c x * g c x)) ^ 2 :=
      probabilityWeighted_square_le p _ hp hsum
    _ ≤ ∑ c, p c * (C ^ 2 * finiteHaarMean
        (fun x => finiteHaarMean (fun a : Q => g c x * g c (x + a)))) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (subgroup_invariant_factor_cauchy Q (f c) (g c) C (hf c) (hinv c)) (hp c))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring

end Hindman168
