import Hindman168.FiniteHaarMean
import Hindman168.CoprimeMultipleSubgroups
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Actual real subgroup cube products and their normalized means.
These are cube means (powers in the Gowers convention), not yet norms. -/
namespace Hindman168
open scoped BigOperators Classical

variable {G : Type*} [AddCommGroup G]

noncomputable def subgroupCubeProduct (Q : AddSubgroup G) (d : ℕ)
    (h : G → ℝ) (x : G) (v : Fin d → Q) : ℝ :=
  ∏ ω : Finset (Fin d), h (x + ∑ j ∈ ω, (v j : G))

noncomputable def subgroupCubeAverage [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (h : G → ℝ) : ℝ :=
  finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q => subgroupCubeProduct Q d h x v))

theorem subgroupCubeProduct_abs_le_one (Q : AddSubgroup G) (d : ℕ) (h : G → ℝ)
    (hh : ∀ x, |h x| ≤ 1) (x : G) (v : Fin d → Q) :
    |subgroupCubeProduct Q d h x v| ≤ 1 := by
  rw [subgroupCubeProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hh _)

theorem subgroupCubeAverage_abs_le_one [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (h : G → ℝ) (hh : ∀ x, |h x| ≤ 1) : |subgroupCubeAverage Q d h| ≤ 1 := by
  apply finiteHaarMean_abs_le_one
  intro x
  exact finiteHaarMean_abs_le_one _ (subgroupCubeProduct_abs_le_one Q d h hh x)

theorem subgroupCubeAverage_one [Fintype G] (Q : AddSubgroup G) [Fintype Q] (d : ℕ) :
    subgroupCubeAverage Q d (fun _ => 1) = 1 := by
  simp only [subgroupCubeAverage, subgroupCubeProduct, Finset.prod_const_one, finiteHaarMean_const]

noncomputable def weightedSubgroupCubeAverage {ι : Type*} [Fintype ι] [Fintype G]
    (p : ι → ℝ) (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (h : ι → G → ℝ) : ℝ :=
  ∑ c, p c * subgroupCubeAverage Q d (h c)

theorem weightedSubgroupCubeAverage_abs_le_one {ι : Type*} [Fintype ι] [Fintype G]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (h : ι → G → ℝ)
    (hh : ∀ c x, |h c x| ≤ 1) : |weightedSubgroupCubeAverage p Q d h| ≤ 1 := by
  calc
    _ ≤ ∑ c, |p c * subgroupCubeAverage Q d (h c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, p c := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul, abs_of_nonneg (hp c)]
      exact mul_le_of_le_one_right (hp c) (subgroupCubeAverage_abs_le_one Q d (h c) (hh c))
    _ = 1 := hsum

end Hindman168
