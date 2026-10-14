import Hindman168.IteratedDirectionalCauchy
import Hindman168.RetainedRootCube
import Hindman168.SubgroupCubeDerivative
import Hindman168.SubgroupGowersDimensionMonotone

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem iteratedDirectionalMean_root {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G)) (h : G → ℝ) :
    iteratedDirectionalMean k D (fun z => h z.1) = subgroupCubeAverage Q k h := by
  induction k generalizing h with
  | zero =>
    simp only [iteratedDirectionalMean, subgroupCubeAverage_zero, finiteHaarMean_prod,
      finiteHaarMean_const]
  | succ k ih =>
    rw [iteratedDirectionalMean, subgroupCubeAverage_succ_derivative]
    apply congrArg finiteHaarMean
    funext a
    simpa only [Prod.fst_add, hD] using
      ih (fun j => D j.succ) (fun j => hD j.succ) (fun x => h x * h (x + a))

theorem iteratedRootCube_bound {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G))
    (f : Fin k → (G × (Fin d → Q)) → ℝ)
    (hf : ∀ j z, |f j z| ≤ 1) (hi : ∀ j z a, f j (z + D j a) = f j z)
    (h : G → ℝ) :
    finiteHaarMean (fun z => h z.1 * ∏ j, f j z) ^ (2 ^ k) ≤ subgroupCubeAverage Q k h := by
  rw [← iteratedDirectionalMean_root Q D hD h]
  exact iteratedDirectionalCauchy k D
    (fun j => rootResponseDirection_injective Q (D j) (hD j)) f hf hi _

theorem weightedIteratedRootCube_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) {d k : ℕ}
    (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G))
    (f : ι → Fin k → (G × (Fin d → Q)) → ℝ)
    (hf : ∀ c j z, |f c j z| ≤ 1) (hi : ∀ c j z a, f c j (z + D j a) = f c j z)
    (h : ι → G → ℝ) :
    (∑ c, p c * finiteHaarMean (fun z => h c z.1 * ∏ j, f c j z)) ^ (2 ^ k) ≤
      weightedSubgroupCubeAverage p Q k h := by
  exact (probabilityWeighted_pow_two_pow_le p _ hp hsum k).trans
    (Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
      (iteratedRootCube_bound Q D hD (f c) (hf c) (hi c) (h c)) (hp c)))

theorem weightedIteratedRootGowers_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) {d k : ℕ}
    (hk : 0 < k) (D : Fin k → Q →+ (G × (Fin d → Q)))
    (hD : ∀ j a, (D j a).1 = (a : G))
    (f : ι → Fin k → (G × (Fin d → Q)) → ℝ)
    (hf : ∀ c j z, |f c j z| ≤ 1) (hi : ∀ c j z a, f c j (z + D j a) = f c j z)
    (h : ι → G → ℝ) :
    |∑ c, p c * finiteHaarMean (fun z => h c z.1 * ∏ j, f c j z)| ≤
      weightedSubgroupGowersValue Q p k h := by
  have ha (t : ℝ) : |t| ^ (2 ^ k) = t ^ (2 ^ k) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ, pow_mul, pow_mul, ← abs_pow, sq_abs]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero k (show (2 : ℕ) ≠ 0 by decide))
    (weightedSubgroupGowersValue_nonneg Q p hp k hk h)
  rw [ha, weightedSubgroupGowersValue_pow Q p hp k hk]
  simp only [subgroupGowersValue_pow Q k hk]
  exact weightedIteratedRootCube_bound Q p hp hsum D hD f hf hi h

end Hindman168
