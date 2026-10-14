import Hindman168.SubgroupCubeDerivative
import Hindman168.SubgroupBesselEnergy

/-! Exact pair-shift derivative moments for the original weighted cube law. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G)

theorem subgroupCubeProduct_translate (d : ℕ) (h : G → ℝ) (a x : G)
    (v : Fin d → Q) :
    subgroupCubeProduct Q d (fun y => h (y + a)) x v =
      subgroupCubeProduct Q d h (x + a) v := by
  unfold subgroupCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  change h ((x + ∑ j ∈ ω, (v j : G)) + a) = h ((x + a) + ∑ j ∈ ω, (v j : G))
  congr 1
  exact add_right_comm x _ a

theorem subgroupCubeAverage_translate [Fintype G] [Fintype Q]
    (d : ℕ) (h : G → ℝ) (a : G) :
    subgroupCubeAverage Q d (fun y => h (y + a)) = subgroupCubeAverage Q d h := by
  unfold subgroupCubeAverage
  simp only [subgroupCubeProduct_translate]
  simpa only [add_comm] using finiteHaarMean_add_left
    (fun x => finiteHaarMean (fun v : Fin d → Q => subgroupCubeProduct Q d h x v)) a

theorem subgroupCubeAverage_pair_derivative [Fintype G] [Fintype Q]
    (d : ℕ) (h : G → ℝ) :
    finiteHaarMean (fun a : Q => finiteHaarMean (fun b : Q =>
      subgroupCubeAverage Q d (fun x => h (x + a) * h (x + b)))) =
        subgroupCubeAverage Q (d + 1) h := by
  have hpair (a b : Q) :
      subgroupCubeAverage Q d (fun x => h (x + a) * h (x + b)) =
        subgroupCubeAverage Q d (fun x => h x * h (x + (b - a : Q))) := by
    have he : (fun x : G => h (x + a) * h (x + b)) =
        (fun x : G => (fun y => h y * h (y + (b - a : Q))) (x + a)) := by
      funext x
      simp only [AddSubgroup.coe_sub]
      congr 2
      abel
    rw [he]
    exact subgroupCubeAverage_translate Q d (fun y => h y * h (y + (b - a : Q))) (a : G)
  simp_rw [hpair]
  have hmean (a : Q) : finiteHaarMean (fun b : Q =>
      subgroupCubeAverage Q d (fun x => h x * h (x + (b - a : Q)))) =
        subgroupCubeAverage Q (d + 1) h := by
    rw [subgroupCubeAverage_succ_derivative]
    simpa only [sub_eq_add_neg, add_comm] using finiteHaarMean_add_left
      (fun b : Q => subgroupCubeAverage Q d (fun x => h x * h (x + b))) (-a)
  simp only [hmean, finiteHaarMean_const]

theorem weightedSubgroupGowersValue_pair_moment {κ : Type*} [Fintype κ]
    [Fintype G] [Fintype Q] (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c)
    (d : ℕ) (hd : 0 < d) (h : κ → G → ℝ) :
    finiteHaarMean (fun a : Q => finiteHaarMean (fun b : Q =>
      weightedSubgroupGowersValue Q p d
        (fun c x => h c (x + a) * h c (x + b)) ^ (2 ^ d))) =
      weightedSubgroupGowersValue Q p (d + 1) h ^ (2 ^ (d + 1)) := by
  simp only [weightedSubgroupGowersValue_pow Q p hp d hd,
    weightedSubgroupGowersValue_pow Q p hp (d + 1) (Nat.succ_pos d),
    subgroupGowersValue_pow Q d hd, subgroupGowersValue_pow Q (d + 1) (Nat.succ_pos d)]
  simp only [finiteHaarMean_sum, finiteHaarMean_const_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [subgroupCubeAverage_pair_derivative]

end Hindman168
