import Hindman168.SubgroupInvariantFactorCauchy
import Mathlib.Tactic.Abel

/-! The paper's root and vertex-fixing directions on the actual cube
parameter group. Their action fixes every translated copy of that vertex. -/
namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] (Q : AddSubgroup G) (d : ℕ)

def cubeVertexEvaluation (ω : Finset (Fin d)) (z : G × (Fin d → Q)) : G :=
  z.1 + ∑ j ∈ ω, (z.2 j : G)

def subgroupCubeRootDirection : Q →+ (G × (Fin d → Q)) where
  toFun a := ((a : G), 0)
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

def cubeVertexFixingDirection (j : Fin d) : Q →+ (G × (Fin d → Q)) where
  toFun a := ((a : G), fun k => if k = j then -a else 0)
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext k
    · simp
    · by_cases hk : k = j <;> simp [hk, add_comm]

theorem cubeVertexEvaluation_add (ω : Finset (Fin d)) (z b : G × (Fin d → Q)) :
    cubeVertexEvaluation Q d ω (z + b) =
      cubeVertexEvaluation Q d ω z + cubeVertexEvaluation Q d ω b := by
  simp only [cubeVertexEvaluation, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    AddSubgroup.coe_add, Finset.sum_add_distrib]
  abel

theorem cubeVertexEvaluation_fixingDirection (ω : Finset (Fin d))
    (j : Fin d) (hj : j ∈ ω) (a : Q) :
    cubeVertexEvaluation Q d ω (cubeVertexFixingDirection Q d j a) = 0 := by
  simp [cubeVertexEvaluation, cubeVertexFixingDirection, apply_ite, hj]

theorem cubeVertexEvaluation_translated_copy_fixed (ω : Finset (Fin d))
    (j : Fin d) (hj : j ∈ ω) (z b : G × (Fin d → Q)) (a : Q) :
    cubeVertexEvaluation Q d ω (z + cubeVertexFixingDirection Q d j a + b) =
      cubeVertexEvaluation Q d ω (z + b) := by
  simp only [cubeVertexEvaluation_add, cubeVertexEvaluation_fixingDirection Q d ω j hj,
    add_zero]

theorem cubeVertexEvaluation_root_response (j : Fin d) (z : G × (Fin d → Q)) (a : Q) :
    cubeVertexEvaluation Q d ∅ (z + cubeVertexFixingDirection Q d j a) =
      cubeVertexEvaluation Q d ∅ z + a := by
  simp [cubeVertexEvaluation, cubeVertexFixingDirection]

theorem subgroupCubeRootDirection_preserves_increments (z : G × (Fin d → Q)) (a : Q) :
    (z + subgroupCubeRootDirection Q d a).2 = z.2 := by
  simp [subgroupCubeRootDirection]

theorem cubeParameterDirections_commute (z b c : G × (Fin d → Q)) :
    z + b + c = z + c + b := add_right_comm _ _ _

end Hindman168
