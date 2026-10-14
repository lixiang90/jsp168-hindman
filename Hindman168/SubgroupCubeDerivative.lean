import Hindman168.SubgroupCubePositive

/-! Exact multiplicative-difference recursion for the original real
subgroup cube mean, without altering its normalization. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G)

theorem subgroupCubeProduct_mul (d : ℕ) (h k : G → ℝ) (x : G) (v : Fin d → Q) :
    subgroupCubeProduct Q d (fun y => h y * k y) x v =
      subgroupCubeProduct Q d h x v * subgroupCubeProduct Q d k x v := by
  simp only [subgroupCubeProduct, Finset.prod_mul_distrib]

theorem subgroupCubeProduct_succ_derivative (d : ℕ) (h : G → ℝ)
    (x : G) (a : Q) (v : Fin d → Q) :
    subgroupCubeProduct Q (d + 1) h x (Fin.cons a v) =
      subgroupCubeProduct Q d (fun y => h y * h (y + a)) x v := by
  rw [subgroupCubeProduct_succ, subgroupCubeProduct_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, subgroupCubeProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro ω _
  congr 1
  exact add_right_comm x _ _

theorem subgroupCubeAverage_succ_derivative [Fintype G] [Fintype Q]
    (d : ℕ) (h : G → ℝ) :
    subgroupCubeAverage Q (d + 1) h = finiteHaarMean
      (fun a : Q => subgroupCubeAverage Q d (fun y => h y * h (y + a))) := by
  unfold subgroupCubeAverage
  simp only [finiteHaarMean_fin_succ, subgroupCubeProduct_succ_derivative]
  exact finiteHaarMean_comm _

end Hindman168

