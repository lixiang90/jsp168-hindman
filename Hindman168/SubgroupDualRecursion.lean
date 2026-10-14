import Hindman168.SubgroupDualEnergy
import Hindman168.SubgroupCubeDerivative

namespace Hindman168
open scoped BigOperators Classical

theorem prod_nonempty_powerset_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (f : Finset ι → ℝ) :
    (∏ ω ∈ (insert a s).powerset.erase ∅, f ω) =
      (∏ ω ∈ s.powerset.erase ∅, f ω) * ∏ ω ∈ s.powerset, f (insert a ω) := by
  have hn : (∅ : Finset ι) ∉ s.powerset.image (insert a) := by simp
  rw [Finset.powerset_insert, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn]
  rw [Finset.prod_union, Finset.prod_image]
  · exact Finset.insert_erase_invOn.2.injOn.mono (fun t ht =>
      Finset.notMem_mono (Finset.mem_powerset.mp ht) ha)
  · apply Finset.disjoint_left.mpr
    intro ω hω him
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp him
    exact ha (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hω) (Finset.mem_insert_self a t))

theorem nonrootCubeProduct_image {ι κ G : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup G]
    (s : Finset ι) (e : ι → κ) (he : Function.Injective e) (v : κ → G) (f : G → ℝ) (x : G) :
    (∏ ω ∈ (s.image e).powerset.erase ∅, f (x + ∑ j ∈ ω, v j)) =
      ∏ ω ∈ s.powerset.erase ∅, f (x + ∑ j ∈ ω, v (e j)) := by
  have hi : (s.image e).powerset.erase ∅ = (s.powerset.erase ∅).image (Finset.image e) := by
    rw [Finset.powerset_image, Finset.image_erase (Finset.image_injective he)]
    simp only [Finset.image_empty]
  rw [hi, Finset.prod_image (Finset.image_injective he).injOn]
  simp only [Finset.sum_image he.injOn]

theorem nonrootCubeProduct_succ_derivative {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) (d : ℕ) (f : G → ℝ) (x : G) (a : Q) (v : Fin d → Q) :
    (∏ ω ∈ (Finset.univ : Finset (Finset (Fin (d + 1)))).erase ∅,
      f (x + ∑ j ∈ ω, ((Fin.cons a v : Fin (d + 1) → Q) j : G))) =
      f (x + a) * (∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        (f (x + ∑ j ∈ ω, (v j : G)) * f (x + (∑ j ∈ ω, (v j : G)) + a))) := by
  have hu : (Finset.univ : Finset (Fin (d + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← Finset.powerset_univ (α := Fin (d + 1)), hu, prod_nonempty_powerset_insert _ _ (by simp)]
  have hs (ω : Finset (Fin (d + 1))) (hω : ω ∈ (Finset.univ.image Fin.succ).powerset) :
      f (x + ∑ j ∈ insert 0 ω, ((Fin.cons a v : Fin (d + 1) → Q) j : G)) =
        f ((x + a) + ∑ j ∈ ω, ((Fin.cons a v : Fin (d + 1) → Q) j : G)) := by
    have hz : (0 : Fin (d + 1)) ∉ ω := by
      intro hm
      have := Finset.mem_powerset.mp hω hm
      simp at this
    rw [Finset.sum_insert hz]
    simp only [Fin.cons_zero, add_assoc]
  rw [Finset.prod_congr rfl hs]
  rw [nonrootCubeProduct_image _ Fin.succ (Fin.succ_injective d),
    cubeProduct_image _ Fin.succ (Fin.succ_injective d)]
  simp only [Fin.cons_succ, Finset.powerset_univ]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
  simp only [Finset.sum_empty, add_zero, Finset.prod_mul_distrib, add_right_comm]
  ring

theorem subgroupDualFunction_succ {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) (x : G) :
    subgroupDualFunction Q (d + 1) f x = finiteHaarMean
      (fun a : Q => f (x + a) * subgroupDualFunction Q d (fun y => f y * f (y + a)) x) := by
  unfold subgroupDualFunction
  rw [finiteHaarMean_fin_succ]
  simp only [nonrootCubeProduct_succ_derivative, finiteHaarMean_const_mul]

theorem subgroupDualFunction_zero {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : G → ℝ) (x : G) :
    subgroupDualFunction Q 0 f x = 1 := by
  have he : (Finset.univ : Finset (Finset (Fin 0))).erase ∅ = ∅ := by decide
  simp only [subgroupDualFunction, he, Finset.prod_empty, finiteHaarMean_const]

theorem subgroupDualFunction_translate {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : G → ℝ) (a x : G) :
    subgroupDualFunction Q d (fun y => f (y + a)) x = subgroupDualFunction Q d f (x + a) := by
  unfold subgroupDualFunction
  congr 1
  funext v
  apply Finset.prod_congr rfl
  intro ω _
  exact congrArg f (add_right_comm x _ a)

end Hindman168
