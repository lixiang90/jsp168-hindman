import Hindman168.MixedCubeFaceCauchySchwarz

namespace Hindman168
open scoped BigOperators Classical

noncomputable def cubeFaceCopy {G : Type*} (d : ℕ) (i : Fin d) (b : Bool)
    (f : Finset (Fin d) → G → ℝ) : Finset (Fin d) → G → ℝ :=
  fun ω => f (if b then insert i ω else ω.erase i)

theorem cubeFaceCopy_twice {G : Type*} (d : ℕ) (i : Fin d) (a b : Bool)
    (f : Finset (Fin d) → G → ℝ) :
    cubeFaceCopy d i b (cubeFaceCopy d i a f) = cubeFaceCopy d i a f := by
  funext ω x
  cases a <;> cases b <;> by_cases hi : i ∈ ω <;> simp [cubeFaceCopy, hi]

theorem subgroupMixedCubeAverage_faceCopy_false {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) :
    subgroupMixedCubeAverage Q (d + 1) (cubeFaceCopy (d + 1) 0 false f) =
      finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        (subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (ω.image Fin.succ) (y + ∑ j ∈ ω, (v j : G))) x) ^ 2)) := by
  rw [subgroupMixedCubeAverage_face_correlation]
  have hz (ω : Finset (Fin d)) : (0 : Fin (d + 1)) ∉ ω.image Fin.succ := by simp
  simp only [cubeFaceCopy, Bool.false_eq_true, ↓reduceIte,
    Finset.erase_insert (hz _), Finset.erase_eq_of_notMem (hz _), pow_two]

theorem subgroupMixedCubeAverage_faceCopy_true {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) :
    subgroupMixedCubeAverage Q (d + 1) (cubeFaceCopy (d + 1) 0 true f) =
      finiteHaarMean (fun v : Fin d → Q => finiteHaarMean (fun x =>
        (subgroupHaarMean Q (fun y => ∏ ω : Finset (Fin d),
          f (insert 0 (ω.image Fin.succ)) (y + ∑ j ∈ ω, (v j : G))) x) ^ 2)) := by
  rw [subgroupMixedCubeAverage_face_correlation]
  simp only [cubeFaceCopy, ↓reduceIte, Finset.insert_idem, pow_two]

theorem subgroupMixedCubeAverage_faceCopy_nonneg {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (b : Bool) (f : Finset (Fin (d + 1)) → G → ℝ) :
    0 ≤ subgroupMixedCubeAverage Q (d + 1) (cubeFaceCopy (d + 1) 0 b f) := by
  cases b
  · rw [subgroupMixedCubeAverage_faceCopy_false]
    exact finiteHaarMean_nonneg _ (fun v => finiteHaarMean_nonneg _ (fun x => sq_nonneg _))
  · rw [subgroupMixedCubeAverage_faceCopy_true]
    exact finiteHaarMean_nonneg _ (fun v => finiteHaarMean_nonneg _ (fun x => sq_nonneg _))

theorem subgroupMixedCubeAverage_face_reflection_bound {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : Finset (Fin (d + 1)) → G → ℝ) :
    subgroupMixedCubeAverage Q (d + 1) f ^ 2 ≤
      subgroupMixedCubeAverage Q (d + 1) (cubeFaceCopy (d + 1) 0 false f) *
      subgroupMixedCubeAverage Q (d + 1) (cubeFaceCopy (d + 1) 0 true f) := by
  rw [subgroupMixedCubeAverage_faceCopy_false, subgroupMixedCubeAverage_faceCopy_true]
  exact subgroupMixedCubeAverage_face_cauchy_schwarz Q d f

theorem cubeFaceCopy_commute {G : Type*} (d : ℕ) (i j : Fin d) (hij : i ≠ j)
    (a b : Bool) (f : Finset (Fin d) → G → ℝ) :
    cubeFaceCopy d i a (cubeFaceCopy d j b f) =
      cubeFaceCopy d j b (cubeFaceCopy d i a f) := by
  funext ω x
  cases a <;> cases b <;> simp only [cubeFaceCopy, Bool.false_eq_true, ↓reduceIte]
  all_goals
    apply congrArg (fun s => f s x)
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

end Hindman168
