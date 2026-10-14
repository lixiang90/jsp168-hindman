import Hindman168.SubgroupDualAntiuniformity

namespace Hindman168
open scoped BigOperators Classical symmDiff

noncomputable def subgroupMixedDualFunction {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ) (x : G) : ℝ :=
  finiteHaarMean (fun v : Fin d → Q =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, f ω (x + ∑ j ∈ ω, (v j : G)))

theorem subgroupMixedDualFunction_eq_vertexDual {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ) :
    subgroupMixedDualFunction Q d f = subgroupVertexDual Q d ∅ f := by
  have he (T : Finset (Fin d)) : (∅ : Finset (Fin d)) ∆ T = T := by
    ext k
    simp [Finset.mem_symmDiff]
  funext x
  simp only [subgroupMixedDualFunction, subgroupVertexDual, he]

theorem finset_fin_succ_nonempty_product (d : ℕ) (F : Finset (Fin (d + 1)) → ℝ) :
    (∏ ω ∈ (Finset.univ : Finset (Finset (Fin (d + 1)))).erase ∅, F ω) =
      F {0} * ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        (F (ω.image Fin.succ) * F (insert 0 (ω.image Fin.succ))) := by
  have hu : (Finset.univ : Finset (Fin (d + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hi : (Finset.univ.image (Fin.succ : Fin d → Fin (d + 1))).powerset.erase ∅ =
      ((Finset.univ : Finset (Fin d)).powerset.erase ∅).image (Finset.image Fin.succ) := by
    rw [Finset.powerset_image, Finset.image_erase (Finset.image_injective (Fin.succ_injective d))]
    simp only [Finset.image_empty]
  rw [← Finset.powerset_univ (α := Fin (d + 1)), hu, prod_nonempty_powerset_insert _ _ (by simp), hi]
  simp only [Finset.powerset_image,
    Finset.prod_image (Finset.image_injective (Fin.succ_injective d)).injOn, Finset.powerset_univ]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
  simp only [Finset.image_empty, Finset.insert_empty, Finset.prod_mul_distrib]
  ring

theorem mixedNonrootCubeProduct_succ {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ)
    (x : G) (a : Q) (v : Fin d → Q) :
    (∏ ω ∈ (Finset.univ : Finset (Finset (Fin (d + 1)))).erase ∅,
      f ω (x + ∑ j ∈ ω, ((Fin.cons a v : Fin (d + 1) → Q) j : G))) =
      f {0} (x + a) * ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        (f (ω.image Fin.succ) (x + ∑ j ∈ ω, (v j : G)) *
          f (insert 0 (ω.image Fin.succ)) (x + (∑ j ∈ ω, (v j : G)) + a)) := by
  rw [finset_fin_succ_nonempty_product]
  simp only [Finset.sum_singleton, Fin.cons_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro ω _
  have hz : (0 : Fin (d + 1)) ∉ ω.image Fin.succ := by simp
  rw [Finset.sum_insert hz, Finset.sum_image (Fin.succ_injective d).injOn]
  simp only [Fin.cons_zero, Fin.cons_succ, add_left_comm, add_comm]

theorem subgroupMixedDualFunction_succ {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) (x : G) :
    subgroupMixedDualFunction Q (d + 1) f x = finiteHaarMean (fun a : Q =>
      f {0} (x + a) * subgroupMixedDualFunction Q d
        (fun ω y => f (ω.image Fin.succ) y * f (insert 0 (ω.image Fin.succ)) (y + a)) x) := by
  unfold subgroupMixedDualFunction
  rw [finiteHaarMean_fin_succ]
  simp only [mixedNonrootCubeProduct_succ, finiteHaarMean_const_mul]

theorem subgroupMixedDualFunction_translate {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ) (a x : G) :
    subgroupMixedDualFunction Q d (fun ω y => f ω (y + a)) x =
      subgroupMixedDualFunction Q d f (x + a) := by
  unfold subgroupMixedDualFunction
  congr 1
  funext v
  apply Finset.prod_congr rfl
  intro ω _
  exact congrArg (f ω) (add_right_comm x _ a)

theorem subgroupMixedDualFunction_subgroup_translate_expansion {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ)
    (n : Q) (x : G) :
    subgroupMixedDualFunction Q (d + 1) f (x + n) = finiteHaarMean (fun h : Q =>
      f {0} (x + h) * subgroupMixedDualFunction Q d (fun ω y =>
        f (ω.image Fin.succ) (y + n) * f (insert 0 (ω.image Fin.succ)) (y + h)) x) := by
  let H := fun h : Q => f {0} (x + h) * subgroupMixedDualFunction Q d (fun ω y =>
    f (ω.image Fin.succ) (y + n) * f (insert 0 (ω.image Fin.succ)) (y + h)) x
  have he (a : Q) : f {0} (x + n + a) * subgroupMixedDualFunction Q d
      (fun ω y => f (ω.image Fin.succ) y * f (insert 0 (ω.image Fin.succ)) (y + a)) (x + n) = H (n + a) := by
    rw [← subgroupMixedDualFunction_translate Q d
      (fun ω y => f (ω.image Fin.succ) y * f (insert 0 (ω.image Fin.succ)) (y + a)) (n : G) x]
    simp only [H, AddSubgroup.coe_add, add_assoc]
  rw [subgroupMixedDualFunction_succ]
  simp_rw [he]
  exact finiteHaarMean_add_left H n

end Hindman168
