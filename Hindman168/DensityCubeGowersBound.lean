import Hindman168.DensityCubeFactors

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedUnitDensityCube_gowers_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) (d : ℕ)
    (ρ : ι → (Fin d → Q) → ℝ) (hρ : ∀ c v, |ρ c v| ≤ 1)
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean
      (fun v => ρ c v * subgroupCubeProduct Q d (h c) x v))| ≤
        weightedSubgroupGowersValue Q p (2 ^ d) h := by
  have hb := weightedIndexedRootGowers_bound Q p hp hsum
    (densityCubeDirection Q d) (densityCubeDirection_root Q d)
    (fun c => densityCubeFactor Q d (ρ c) (h c))
    (fun c => densityCubeFactor_bound Q d (ρ c) (h c) (hρ c) (hh c))
    (fun c => densityCubeFactor_invariant Q d (ρ c) (h c)) h
  simpa only [densityCubeFactor_product, Fintype.card_finset, Fintype.card_fin,
    finiteHaarMean_prod] using hb

theorem weightedDensityCube_gowers_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) (d : ℕ)
    (C : ℝ) (hC : 0 < C) (ρ : ι → (Fin d → Q) → ℝ) (hρ : ∀ c v, |ρ c v| ≤ C)
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1) :
    |∑ c, p c * finiteHaarMean (fun x => finiteHaarMean
      (fun v => ρ c v * subgroupCubeProduct Q d (h c) x v))| ≤
        C * weightedSubgroupGowersValue Q p (2 ^ d) h := by
  let q : ι → (Fin d → Q) → ℝ := fun c v => ρ c v / C
  have hq (c : ι) (v : Fin d → Q) : |q c v| ≤ 1 := by
    dsimp [q]
    rw [abs_div, abs_of_pos hC]
    exact (div_le_one hC).mpr (hρ c v)
  have he (c : ι) (v : Fin d → Q) : ρ c v = C * q c v := by
    dsimp [q]
    field_simp
  have hs : (∑ c, p c * finiteHaarMean (fun x => finiteHaarMean
      (fun v => ρ c v * subgroupCubeProduct Q d (h c) x v))) =
      C * ∑ c, p c * finiteHaarMean (fun x => finiteHaarMean
      (fun v => q c v * subgroupCubeProduct Q d (h c) x v)) := by
    simp only [he, mul_assoc, finiteHaarMean_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hs, abs_mul, abs_of_pos hC]
  exact mul_le_mul_of_nonneg_left
    (weightedUnitDensityCube_gowers_bound Q p hp hsum d q hq h hh) hC.le

end Hindman168
