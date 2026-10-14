import Hindman168.WeightedDualApproximation
import Mathlib.Data.Finset.SymmDiff

namespace Hindman168
open scoped BigOperators Classical symmDiff

noncomputable def cubeDirectionReflection {G : Type*} [AddCommGroup G] (d : ℕ)
    (S : Finset (Fin d)) : (Fin d → G) ≃ (Fin d → G) where
  toFun v := fun j => if j ∈ S then -v j else v j
  invFun v := fun j => if j ∈ S then -v j else v j
  left_inv v := by funext j; by_cases hj : j ∈ S <;> simp [hj]
  right_inv v := by funext j; by_cases hj : j ∈ S <;> simp [hj]

theorem cube_reflection_vertex {G : Type*} [AddCommGroup G] (d : ℕ)
    (S ω : Finset (Fin d)) (v : Fin d → G) :
    (∑ j ∈ S, v j) + (∑ j ∈ ω, cubeDirectionReflection d S v j) =
      ∑ j ∈ S ∆ ω, v j := by
  have hs (s : Finset (Fin d)) (h : Fin d → G) :
      (∑ j ∈ s, h j) = ∑ j, if j ∈ s then h j else 0 := by simp
  rw [hs S v, hs ω _, hs (S ∆ ω) v, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hS : j ∈ S <;> by_cases hω : j ∈ ω <;>
    simp [cubeDirectionReflection, hS, hω, Finset.mem_symmDiff]

theorem subgroupCube_reflection_mean {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (F : G → (Fin d → Q) → ℝ) :
    finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q =>
      F (x + ∑ j ∈ S, (v j : G)) (cubeDirectionReflection d S v))) =
      finiteHaarMean (fun x => finiteHaarMean (F x)) := by
  rw [finiteHaarMean_comm]
  have ht (v : Fin d → Q) :
      finiteHaarMean (fun x => F (x + ∑ j ∈ S, (v j : G)) (cubeDirectionReflection d S v)) =
        finiteHaarMean (fun x => F x (cubeDirectionReflection d S v)) :=
    finiteHaarMean_equiv (Equiv.addRight (∑ j ∈ S, (v j : G))) (fun x => F x (cubeDirectionReflection d S v))
  simp_rw [ht]
  exact (finiteHaarMean_equiv (cubeDirectionReflection d S)
    (fun v => finiteHaarMean (fun x => F x v))).trans (finiteHaarMean_comm F).symm

theorem subgroupCube_mixed_vertex_reflection {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) :
    finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q =>
      ∏ ω : Finset (Fin d), f ω (x + ∑ j ∈ S ∆ ω, (v j : G)))) =
      finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q =>
        ∏ ω : Finset (Fin d), f ω (x + ∑ j ∈ ω, (v j : G)))) := by
  have he (v : Fin d → Q) (ω : Finset (Fin d)) :
      (∑ j ∈ S, (v j : G)) + (∑ j ∈ ω, (cubeDirectionReflection (G := Q) d S v j : G)) =
        ∑ j ∈ S ∆ ω, (v j : G) := by
    have h := congrArg Q.subtype (cube_reflection_vertex d S ω v)
    simpa only [map_add, map_sum, AddSubgroup.subtype_apply] using h
  have hm := subgroupCube_reflection_mean Q d S (fun x v =>
    ∏ ω : Finset (Fin d), f ω (x + ∑ j ∈ ω, (v j : G)))
  simpa only [add_assoc, he] using hm

end Hindman168
