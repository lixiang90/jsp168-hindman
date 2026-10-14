import Hindman168.CubeVertexFixingDirections

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G) (d : ℕ)

theorem cubeVertexCopies_invariant {ι : Type*} (s : Finset ι)
    (b : ι → G × (Fin d → Q)) (h : G → ℝ) (ω : Finset (Fin d))
    (j : Fin d) (hj : j ∈ ω) (z : G × (Fin d → Q))
    (a : (cubeVertexFixingDirection Q d j).range) :
    (∏ i ∈ s, h (cubeVertexEvaluation Q d ω (z + a + b i))) =
      ∏ i ∈ s, h (cubeVertexEvaluation Q d ω (z + b i)) := by
  obtain ⟨u, hu⟩ := a.property
  rw [← hu]
  simp only [cubeVertexEvaluation_translated_copy_fixed Q d ω j hj]

theorem cubeVertexCopies_abs_le_one {ι : Type*} (s : Finset ι)
    (b : ι → G × (Fin d → Q)) (h : G → ℝ) (hh : ∀ x, |h x| ≤ 1)
    (ω : Finset (Fin d)) (z : G × (Fin d → Q)) :
    |∏ i ∈ s, h (cubeVertexEvaluation Q d ω (z + b i))| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hh _)

theorem cubeDensity_root_invariant (ρ : (Fin d → Q) → ℝ)
    (z : G × (Fin d → Q)) (a : (subgroupCubeRootDirection Q d).range) :
    ρ (z + a).2 = ρ z.2 := by
  obtain ⟨u, hu⟩ := a.property
  rw [← hu, subgroupCubeRootDirection_preserves_increments]

variable [Fintype G] [Fintype Q]

theorem cubeVertexCopies_cauchy {ι : Type*} (s : Finset ι)
    (b : ι → G × (Fin d → Q)) (h : G → ℝ) (hh : ∀ x, |h x| ≤ 1)
    (ω : Finset (Fin d)) (j : Fin d) [Fintype (cubeVertexFixingDirection Q d j).range]
    (hj : j ∈ ω)
    (g : (G × (Fin d → Q)) → ℝ) :
    finiteHaarMean (fun z => (∏ i ∈ s, h (cubeVertexEvaluation Q d ω (z + b i))) * g z) ^ 2 ≤
      finiteHaarMean (fun z => finiteHaarMean
        (fun a : (cubeVertexFixingDirection Q d j).range => g z * g (z + a))) := by
  classical
  simpa only [one_pow, one_mul] using subgroup_invariant_factor_cauchy
    (cubeVertexFixingDirection Q d j).range _ g 1
    (cubeVertexCopies_abs_le_one Q d s b h hh ω)
    (cubeVertexCopies_invariant Q d s b h ω j hj)

theorem cubeDensity_cauchy [Fintype (subgroupCubeRootDirection Q d).range]
    (ρ : (Fin d → Q) → ℝ) (C : ℝ)
    (hρ : ∀ v, |ρ v| ≤ C) (g : (G × (Fin d → Q)) → ℝ) :
    finiteHaarMean (fun z => ρ z.2 * g z) ^ 2 ≤ C ^ 2 *
      finiteHaarMean (fun z => finiteHaarMean
        (fun a : (subgroupCubeRootDirection Q d).range => g z * g (z + a))) := by
  classical
  exact subgroup_invariant_factor_cauchy (subgroupCubeRootDirection Q d).range _ g C
    (fun z => hρ z.2) (cubeDensity_root_invariant Q d ρ)

end Hindman168
