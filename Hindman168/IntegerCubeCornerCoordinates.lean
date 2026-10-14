import Hindman168.SubgroupCubeReflection

namespace Hindman168
open scoped BigOperators Classical symmDiff

/-- Actual integer value of a cube vertex, with signed integer increments. -/
def integerCubeVertex {d : ℕ} (p : ℤ × (Fin d → ℤ)) (ω : Finset (Fin d)) : ℤ :=
  p.1 + ∑ j ∈ ω, p.2 j

/-- One corner and its d adjacent vertices determine the integer cube. -/
def integerCubeCornerCoordinates {d : ℕ} (ω : Finset (Fin d))
    (p : ℤ × (Fin d → ℤ)) : ℤ × (Fin d → ℤ) :=
  (integerCubeVertex p ω, fun j => integerCubeVertex p (ω ∆ {j}))

theorem integerCubeVertex_add {d : ℕ} (p r : ℤ × (Fin d → ℤ)) (ω : Finset (Fin d)) :
    integerCubeVertex (p + r) ω = integerCubeVertex p ω + integerCubeVertex r ω := by
  simp only [integerCubeVertex, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem integerCubeVertex_neighbor {d : ℕ} (p : ℤ × (Fin d → ℤ))
    (ω : Finset (Fin d)) (j : Fin d) :
    integerCubeVertex p (ω ∆ {j}) = integerCubeVertex p ω +
      if j ∈ ω then -p.2 j else p.2 j := by
  have he := cube_reflection_vertex d ω {j} p.2
  simpa only [integerCubeVertex, Finset.sum_singleton, cubeDirectionReflection,
    Equiv.coe_fn_mk, add_assoc] using
    congrArg (fun z : ℤ => p.1 + z) he.symm

theorem integerCubeCornerCoordinates_injective {d : ℕ} (ω : Finset (Fin d)) :
    Function.Injective (integerCubeCornerCoordinates ω) := by
  intro p q he
  have hr : integerCubeVertex p ω = integerCubeVertex q ω := congrArg Prod.fst he
  have hv : p.2 = q.2 := by
    funext j
    have hn : integerCubeVertex p (ω ∆ {j}) = integerCubeVertex q (ω ∆ {j}) :=
      congrArg (fun z : ℤ × (Fin d → ℤ) => z.2 j) he
    rw [integerCubeVertex_neighbor, integerCubeVertex_neighbor] at hn
    by_cases hj : j ∈ ω
    · simp only [if_pos hj] at hn
      linarith
    · simp only [if_neg hj] at hn
      linarith
  apply Prod.ext _ hv
  change p.1 + (∑ j ∈ ω, p.2 j) = q.1 + (∑ j ∈ ω, q.2 j) at hr
  rw [hv] at hr
  exact add_right_cancel hr

end Hindman168
