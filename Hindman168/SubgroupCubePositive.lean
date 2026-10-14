import Hindman168.CubeProductSplitting
import Hindman168.FiniteHaarDirections
import Hindman168.SubgroupHaarSquare

/-! All positive-dimensional actual subgroup cube averages are means
of squares of subgroup-averaged faces. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem subgroupCubeAverage_succ_square (d : ℕ) (h : G → ℝ) :
    subgroupCubeAverage Q (d + 1) h =
      finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        (subgroupHaarMean Q (fun y => subgroupCubeProduct Q d h y v) x) ^ 2)) := by
  unfold subgroupCubeAverage
  simp only [finiteHaarMean_fin_succ, subgroupCubeProduct_succ, Fin.cons_zero, Fin.cons_succ]
  rw [finiteHaarMean_rotate]
  congr 1
  funext v
  exact subgroupHaar_correlation_square Q (fun x => subgroupCubeProduct Q d h x v)

theorem subgroupCubeAverage_nonneg (d : ℕ) (hd : 0 < d) (h : G → ℝ) :
    0 ≤ subgroupCubeAverage Q d h := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [subgroupCubeAverage_succ_square]
  exact finiteHaarMean_nonneg _ (fun v => finiteHaarMean_nonneg _ (fun x => sq_nonneg _))

theorem weightedSubgroupCubeAverage_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (d : ℕ) (hd : 0 < d) (h : ι → G → ℝ) :
    0 ≤ weightedSubgroupCubeAverage p Q d h :=
  Finset.sum_nonneg (fun c _ => mul_nonneg (hp c) (subgroupCubeAverage_nonneg Q d hd (h c)))

end Hindman168
