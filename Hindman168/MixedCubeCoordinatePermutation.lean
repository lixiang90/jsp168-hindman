import Hindman168.MixedCubeFaceCopy

/-! Coordinate reindexing and face reflection for the actual subgroup Haar cube law. -/
namespace Hindman168
open scoped BigOperators Classical

theorem subgroupMixedCubeAverage_permute {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (e : Equiv.Perm (Fin d)) (f : Finset (Fin d) → G → ℝ) :
    subgroupMixedCubeAverage Q d (fun ω => f (ω.image e)) = subgroupMixedCubeAverage Q d f := by
  unfold subgroupMixedCubeAverage
  congr 1
  funext x
  let E : (Fin d → Q) ≃ (Fin d → Q) := {
    toFun := fun v j => v (e j)
    invFun := fun v j => v (e.symm j)
    left_inv := by intro v; funext j; simp
    right_inv := by intro v; funext j; simp }
  let F := fun v : Fin d → Q => ∏ ω : Finset (Fin d), f (ω.image e) (x + ∑ j ∈ ω, (v j : G))
  have he (v : Fin d → Q) : F (E v) =
      ∏ ω : Finset (Fin d), f ω (x + ∑ j ∈ ω, (v j : G)) := by
    dsimp only [F, E, Equiv.coe_fn_mk]
    apply Finset.prod_equiv e.finsetCongr (by simp)
    intro ω _
    simp only [Equiv.finsetCongr_apply, Finset.map_eq_image,
      Equiv.coe_toEmbedding, Finset.sum_image e.injective.injOn]
  simpa only [he] using (finiteHaarMean_equiv E F).symm

theorem cubeFaceCopy_permute {G : Type*} (d : ℕ) (e : Equiv.Perm (Fin d))
    (i : Fin d) (b : Bool) (f : Finset (Fin d) → G → ℝ) :
    cubeFaceCopy d i b (fun ω => f (ω.image e)) =
      fun ω => cubeFaceCopy d (e i) b f (ω.image e) := by
  funext ω x
  cases b <;> simp only [cubeFaceCopy, Bool.false_eq_true, ↓reduceIte,
    Finset.image_insert, Finset.image_erase e.injective]

theorem subgroupMixedCubeAverage_copy_nonneg_any {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (i : Fin d) (b : Bool) (f : Finset (Fin d) → G → ℝ) :
    0 ≤ subgroupMixedCubeAverage Q d (cubeFaceCopy d i b f) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    have h := subgroupMixedCubeAverage_faceCopy_nonneg Q n b (fun ω => f (ω.image e))
    rw [cubeFaceCopy_permute, subgroupMixedCubeAverage_permute, he] at h
    exact h

theorem subgroupMixedCubeAverage_reflection_bound_any {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (i : Fin d) (f : Finset (Fin d) → G → ℝ) :
    subgroupMixedCubeAverage Q d f ^ 2 ≤
      subgroupMixedCubeAverage Q d (cubeFaceCopy d i false f) *
      subgroupMixedCubeAverage Q d (cubeFaceCopy d i true f) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
    have he : e 0 = i := Equiv.swap_apply_left 0 i
    have h := subgroupMixedCubeAverage_face_reflection_bound Q n (fun ω => f (ω.image e))
    rw [subgroupMixedCubeAverage_permute, cubeFaceCopy_permute,
      cubeFaceCopy_permute, subgroupMixedCubeAverage_permute,
      subgroupMixedCubeAverage_permute, he] at h
    exact h

end Hindman168
