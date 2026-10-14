import Hindman168.SubgroupCubeAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fin.Tuple.Basic

namespace Hindman168
open scoped BigOperators Classical

theorem cubeProduct_insert {ι G : Type*} [DecidableEq ι] [AddCommGroup G]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (v : ι → G) (h : G → ℝ) (x : G) :
    (∏ ω ∈ (insert a s).powerset, h (x + ∑ j ∈ ω, v j)) =
      (∏ ω ∈ s.powerset, h (x + ∑ j ∈ ω, v j)) *
      (∏ ω ∈ s.powerset, h ((x + v a) + ∑ j ∈ ω, v j)) := by
  rw [Finset.prod_powerset_insert ha]
  congr 1
  apply Finset.prod_congr rfl
  intro ω hω
  have hn : a ∉ ω := fun hm => ha (Finset.mem_powerset.mp hω hm)
  rw [Finset.sum_insert hn, add_assoc]

theorem cubeProduct_image {ι κ G : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup G]
    (s : Finset ι) (e : ι → κ) (he : Function.Injective e) (v : κ → G) (h : G → ℝ) (x : G) :
    (∏ ω ∈ (s.image e).powerset, h (x + ∑ j ∈ ω, v j)) =
      ∏ ω ∈ s.powerset, h (x + ∑ j ∈ ω, v (e j)) := by
  rw [Finset.powerset_image, Finset.prod_image (Finset.image_injective he).injOn]
  simp only [Finset.sum_image he.injOn]

theorem subgroupCubeProduct_succ {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) (d : ℕ) (h : G → ℝ) (x : G) (v : Fin (d + 1) → Q) :
    subgroupCubeProduct Q (d + 1) h x v =
      subgroupCubeProduct Q d h x (fun j => v j.succ) *
      subgroupCubeProduct Q d h (x + v 0) (fun j => v j.succ) := by
  have hu : (Finset.univ : Finset (Fin (d + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hz : (0 : Fin (d + 1)) ∉ Finset.univ.image Fin.succ := by simp
  unfold subgroupCubeProduct
  rw [← Finset.powerset_univ (α := Fin (d + 1)), hu, cubeProduct_insert _ _ hz]
  rw [cubeProduct_image _ Fin.succ (Fin.succ_injective d),
    cubeProduct_image _ Fin.succ (Fin.succ_injective d)]
  simp only [Finset.powerset_univ]

end Hindman168

