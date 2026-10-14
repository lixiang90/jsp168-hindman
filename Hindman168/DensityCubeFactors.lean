import Hindman168.IndexedRootGowersBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G) (d : ℕ)

def densityCubeDirection (ω : Finset (Fin d)) : Q →+ (G × (Fin d → Q)) :=
  if hω : ω = ∅ then subgroupCubeRootDirection Q d
  else cubeVertexFixingDirection Q d (ω.min' (Finset.nonempty_iff_ne_empty.mpr hω))

def densityCubeFactor (ρ : (Fin d → Q) → ℝ) (h : G → ℝ)
    (ω : Finset (Fin d)) (z : G × (Fin d → Q)) : ℝ :=
  if ω = ∅ then ρ z.2 else h (cubeVertexEvaluation Q d ω z)

theorem densityCubeDirection_root (ω : Finset (Fin d)) (a : Q) :
    (densityCubeDirection Q d ω a).1 = (a : G) := by
  unfold densityCubeDirection
  split <;> rfl

theorem densityCubeFactor_bound (ρ : (Fin d → Q) → ℝ) (h : G → ℝ)
    (hρ : ∀ v, |ρ v| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (ω : Finset (Fin d)) (z : G × (Fin d → Q)) :
    |densityCubeFactor Q d ρ h ω z| ≤ 1 := by
  unfold densityCubeFactor
  split
  · exact hρ _
  · exact hh _

theorem densityCubeFactor_invariant (ρ : (Fin d → Q) → ℝ) (h : G → ℝ)
    (ω : Finset (Fin d)) (z : G × (Fin d → Q)) (a : Q) :
    densityCubeFactor Q d ρ h ω (z + densityCubeDirection Q d ω a) =
      densityCubeFactor Q d ρ h ω z := by
  by_cases hω : ω = ∅
  · simp only [densityCubeFactor, densityCubeDirection, hω, dite_true, ite_true,
      subgroupCubeRootDirection_preserves_increments]
  · simp only [densityCubeFactor, densityCubeDirection, hω, dite_false, ite_false]
    congr 1
    rw [cubeVertexEvaluation_add, cubeVertexEvaluation_fixingDirection Q d ω _
      (Finset.min'_mem ω (Finset.nonempty_iff_ne_empty.mpr hω)), add_zero]

theorem densityCubeFactor_product (ρ : (Fin d → Q) → ℝ) (h : G → ℝ)
    (z : G × (Fin d → Q)) :
    h z.1 * ∏ ω : Finset (Fin d), densityCubeFactor Q d ρ h ω z =
      ρ z.2 * subgroupCubeProduct Q d h z.1 z.2 := by
  classical
  let s := (Finset.univ : Finset (Finset (Fin d))).erase ∅
  have he : (∏ ω, densityCubeFactor Q d ρ h ω z) =
      ρ z.2 * ∏ ω ∈ s, h (cubeVertexEvaluation Q d ω z) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
    simp only [densityCubeFactor, if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro ω hω
    rw [if_neg (Finset.mem_erase.mp hω).1]
  have hc : subgroupCubeProduct Q d h z.1 z.2 =
      h z.1 * ∏ ω ∈ s, h (cubeVertexEvaluation Q d ω z) := by
    change (∏ ω, h (cubeVertexEvaluation Q d ω z)) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (∅ : Finset (Fin d)))]
    simp only [cubeVertexEvaluation, Finset.sum_empty, add_zero]
    rfl
  rw [he, hc]
  ring

end Hindman168
