import Hindman168.MixedCubeIteratedCauchySchwarz
import Hindman168.HaarDyadicPower

namespace Hindman168
open scoped BigOperators Classical symmDiff

theorem subgroupVertexDual_correlation_le_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (S : Finset (Fin d)) (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ T, T ≠ S → ∀ x, |f T x| ≤ 1) (g : G → ℝ) :
    |finiteHaarMean (fun x => g x * subgroupVertexDual Q d S f x)| ≤ subgroupGowersValue Q d g := by
  let F := fun T : Finset (Fin d) => if T = S then g else f T
  have hF : ∀ T, T ≠ S → ∀ x, |F T x| ≤ 1 := by
    intro T hT x
    simpa only [F, if_neg hT] using hf T hT x
  have he : subgroupVertexDual Q d S F = subgroupVertexDual Q d S f :=
    subgroupVertexDual_congr_off_vertex Q d S F f (fun T hT => by simp only [F, if_neg hT])
  have h := subgroupMixedCubeAverage_le_vertex_gowers Q d hd S F hF
  rw [subgroupMixedCubeAverage_vertex_correlation Q d S F, he] at h
  simpa only [F, if_pos rfl] using h

theorem subgroupDualFunction_correlation_le_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (f g : G → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |finiteHaarMean (fun x => g x * subgroupDualFunction Q d f x)| ≤ subgroupGowersValue Q d g := by
  have h := subgroupVertexDual_correlation_le_gowers Q d hd ∅ (fun _ => f) (fun _ _ => hf) g
  have he (T : Finset (Fin d)) : (∅ : Finset (Fin d)) ∆ T = T := by
    ext k
    simp [Finset.mem_symmDiff]
  simpa only [subgroupVertexDual, subgroupDualFunction, he] using h

theorem probabilityWeighted_gowers_le_weightedGowers {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (g : κ → G → ℝ) :
    (∑ c, p c * subgroupGowersValue Q d (g c)) ≤ weightedSubgroupGowersValue Q p d g := by
  apply le_of_pow_le_pow_left₀ (pow_ne_zero d (show (2 : ℕ) ≠ 0 by decide))
    (weightedSubgroupGowersValue_nonneg Q p hp d hd g)
  rw [weightedSubgroupGowersValue_pow Q p hp d hd]
  exact probabilityWeighted_pow_two_pow_le p _ hp hs d

theorem weighted_subgroupVertexDual_correlation_le_gowers {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (S : Finset (Fin d))
    (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f : κ → Finset (Fin d) → G → ℝ)
    (hf : ∀ c T, T ≠ S → ∀ x, |f c T x| ≤ 1) (g : κ → G → ℝ) :
    |∑ c, p c * finiteHaarMean (fun x => g c x * subgroupVertexDual Q d S (f c) x)| ≤
      weightedSubgroupGowersValue Q p d g := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (probabilityWeighted_gowers_le_weightedGowers Q d hd p hp hs g)
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul, abs_of_nonneg (hp c)]
  exact mul_le_mul_of_nonneg_left
    (subgroupVertexDual_correlation_le_gowers Q d hd S (f c) (hf c) (g c)) (hp c)

theorem subgroupGowersValue_zero_iff_dual_orthogonal {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (g : G → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    subgroupGowersValue Q d g = 0 ↔
      ∀ f : G → ℝ, (∀ x, |f x| ≤ 1) →
        finiteHaarMean (fun x => g x * subgroupDualFunction Q d f x) = 0 := by
  constructor
  · intro hz f hf
    apply abs_eq_zero.mp
    exact le_antisymm ((subgroupDualFunction_correlation_le_gowers Q d hd f g hf).trans_eq hz) (abs_nonneg _)
  · intro h
    have he := subgroupGowersValue_pow Q d hd g
    rw [subgroupCubeAverage_dual_correlation, h g hg] at he
    exact eq_zero_of_pow_eq_zero he

end Hindman168
