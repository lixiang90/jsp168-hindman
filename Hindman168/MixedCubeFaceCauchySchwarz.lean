import Hindman168.DualProductExpansion

namespace Hindman168
open scoped BigOperators Classical

theorem finset_fin_succ_product (d : ℕ) (F : Finset (Fin (d + 1)) → ℝ) :
    (∏ ω, F ω) = (∏ ω : Finset (Fin d), F (ω.image Fin.succ)) *
      ∏ ω : Finset (Fin d), F (insert 0 (ω.image Fin.succ)) := by
  have hu : (Finset.univ : Finset (Fin (d + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hz : (0 : Fin (d + 1)) ∉ Finset.univ.image Fin.succ := by simp
  rw [← Finset.powerset_univ (α := Fin (d + 1)), hu, Finset.prod_powerset_insert hz]
  simp only [Finset.powerset_image,
    Finset.prod_image (Finset.image_injective (Fin.succ_injective d)).injOn, Finset.powerset_univ]

theorem mixedCubeProduct_succ {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ)
    (x : G) (a : Q) (v : Fin d → Q) :
    (∏ ω : Finset (Fin (d + 1)), f ω (x + ∑ j ∈ ω, ((Fin.cons a v : Fin (d + 1) → Q) j : G))) =
      (∏ ω : Finset (Fin d), f (ω.image Fin.succ) (x + ∑ j ∈ ω, (v j : G))) *
      ∏ ω : Finset (Fin d), f (insert 0 (ω.image Fin.succ)) (x + a + ∑ j ∈ ω, (v j : G)) := by
  rw [finset_fin_succ_product]
  congr 1
  · apply Finset.prod_congr rfl
    intro ω _
    rw [Finset.sum_image (Fin.succ_injective d).injOn]
    simp only [Fin.cons_succ]
  · apply Finset.prod_congr rfl
    intro ω _
    have hz : (0 : Fin (d + 1)) ∉ ω.image Fin.succ := by simp
    rw [Finset.sum_insert hz, Finset.sum_image (Fin.succ_injective d).injOn]
    simp only [Fin.cons_zero, Fin.cons_succ, add_assoc]

theorem subgroupHaar_cross_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (f g : G → ℝ) :
    finiteHaarMean (fun x => finiteHaarMean (fun a : Q => f x * g (x + a))) =
      finiteHaarMean (fun x => subgroupHaarMean Q f x * subgroupHaarMean Q g x) := by
  rw [subgroupHaarMean_self_adjoint]
  simp_rw [subgroupHaarMean_idempotent]
  simp only [finiteHaarMean_const_mul, subgroupHaarMean]

theorem subgroupMixedCubeAverage_face_correlation {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) :
    subgroupMixedCubeAverage Q (d + 1) f =
      finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (ω.image Fin.succ) (y + ∑ j ∈ ω, (v j : G))) x *
        subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (insert 0 (ω.image Fin.succ)) (y + ∑ j ∈ ω, (v j : G))) x)) := by
  unfold subgroupMixedCubeAverage
  simp only [finiteHaarMean_fin_succ, mixedCubeProduct_succ]
  rw [finiteHaarMean_rotate]
  congr 1
  funext v
  exact subgroupHaar_cross_correlation Q
    (fun y => ∏ ω : Finset (Fin d), f (ω.image Fin.succ) (y + ∑ j ∈ ω, (v j : G)))
    (fun y => ∏ ω : Finset (Fin d), f (insert 0 (ω.image Fin.succ)) (y + ∑ j ∈ ω, (v j : G)))

theorem subgroupMixedCubeAverage_face_cauchy_schwarz {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) :
    subgroupMixedCubeAverage Q (d + 1) f ^ 2 ≤
      (finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        (subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (ω.image Fin.succ) (y + ∑ j ∈ ω, (v j : G))) x) ^ 2))) *
      finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        (subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (insert 0 (ω.image Fin.succ)) (y + ∑ j ∈ ω, (v j : G))) x) ^ 2)) := by
  rw [subgroupMixedCubeAverage_face_correlation]
  simpa only [finiteHaarMean_prod] using finiteHaarMean_cauchy_schwarz
    (fun z : (Fin d → Q) × G => subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
      f (ω.image Fin.succ) (y + ∑ j ∈ ω, (z.1 j : G))) z.2)
    (fun z : (Fin d → Q) × G => subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
      f (insert 0 (ω.image Fin.succ)) (y + ∑ j ∈ ω, (z.1 j : G))) z.2)

end Hindman168
