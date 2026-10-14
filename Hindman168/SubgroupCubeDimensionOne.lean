import Hindman168.SubgroupHaarSquare

/-! Exact identification of the previously defined one-dimensional cube
mean with the subgroup correlation square. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G)

theorem subgroupCubeProduct_one (h : G → ℝ) (x : G) (v : Fin 1 → Q) :
    subgroupCubeProduct Q 1 h x v = h x * h (x + v 0) := by
  have he : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [subgroupCubeProduct, he]

theorem subgroupCubeAverage_one_dimension [Fintype G] [Fintype Q] (h : G → ℝ) :
    subgroupCubeAverage Q 1 h = finiteHaarMean (fun x => (subgroupHaarMean Q h x) ^ 2) := by
  rw [← subgroupHaar_correlation_square]
  unfold subgroupCubeAverage
  congr 1
  funext x
  simp only [subgroupCubeProduct_one]
  exact finiteHaarMean_equiv (Equiv.funUnique (Fin 1) Q) (fun a => h x * h (x + a))

theorem subgroupCubeAverage_one_nonneg [Fintype G] [Fintype Q] (h : G → ℝ) :
    0 ≤ subgroupCubeAverage Q 1 h := by
  rw [subgroupCubeAverage_one_dimension]
  exact finiteHaarMean_nonneg _ (fun _ => sq_nonneg _)

end Hindman168
