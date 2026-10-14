import Hindman168.IndependentRowMinors
import Mathlib.Combinatorics.Colex

/-!
# Explicit integer directions for the prediction cube rows

Binary subset sums replace the paper's finite hyperplane-avoidance choice.
For the row indexed by S, choose a_j = 2^j and a_0 = -sum_{j in S} a_j.
Exactly that cube row is fixed; the root and every other row move.
These constants depend only on the fixed cube template.
-/

namespace Hindman168

open scoped BigOperators Classical

def cubeSubsetCode {d : ℕ} (S : Finset (Fin d)) : ℕ := ∑ j ∈ S, 2 ^ j.val

theorem cubeSubsetCode_pos {d : ℕ} {S : Finset (Fin d)} (hS : S.Nonempty) :
    0 < cubeSubsetCode S := by
  obtain ⟨j, hj⟩ := hS
  exact lt_of_lt_of_le (pow_pos (by omega : 0 < (2 : ℕ)) j.val)
    (Finset.single_le_sum (f := fun j : Fin d => 2 ^ j.val) (fun _ _ => Nat.zero_le _) hj)

theorem cubeSubsetCode_injective (d : ℕ) : Function.Injective (@cubeSubsetCode d) := by
  intro S T h
  apply Finset.image_injective Fin.val_injective
  apply Finset.geomSum_injective (by omega : 2 ≤ (2 : ℕ))
  simpa only [Finset.sum_image (fun _ _ _ _ he => Fin.val_injective he), cubeSubsetCode] using h

theorem cubeSubsetCode_zero_iff {d : ℕ} (S : Finset (Fin d)) :
    cubeSubsetCode S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply cubeSubsetCode_injective d
    simpa only [cubeSubsetCode, Finset.sum_empty] using h
  · rintro rfl
    simp [cubeSubsetCode]

def cubeRootDirection {d : ℕ} (S : Finset (Fin d)) : ℤ := -(cubeSubsetCode S : ℤ)

def cubeShiftDirection {d : ℕ} (j : Fin d) : ℤ := (2 ^ j.val : ℕ)

def cubeDirectionResponse {d : ℕ} (S T : Finset (Fin d)) : ℤ :=
  cubeRootDirection S + ∑ j ∈ T, cubeShiftDirection j

theorem cubeDirectionResponse_eq {d : ℕ} (S T : Finset (Fin d)) :
    cubeDirectionResponse S T = -(cubeSubsetCode S : ℤ) + (cubeSubsetCode T : ℤ) := by
  simp only [cubeDirectionResponse, cubeRootDirection, cubeShiftDirection,
    cubeSubsetCode, Nat.cast_sum]

theorem cubeDirectionResponse_zero_iff {d : ℕ} (S T : Finset (Fin d)) :
    cubeDirectionResponse S T = 0 ↔ S = T := by
  rw [cubeDirectionResponse_eq, neg_add_eq_zero]
  exact Int.ofNat_inj.trans (cubeSubsetCode_injective d).eq_iff

theorem cubeRootDirection_ne_zero {d : ℕ} {S : Finset (Fin d)} (hS : S.Nonempty) :
    cubeRootDirection S ≠ 0 := by
  exact neg_ne_zero.mpr (by exact_mod_cast (cubeSubsetCode_pos hS).ne')

theorem cubeDirectionResponse_self {d : ℕ} (S : Finset (Fin d)) :
    cubeDirectionResponse S S = 0 := (cubeDirectionResponse_zero_iff S S).mpr rfl

theorem cubeDirectionResponse_ne_zero {d : ℕ} {S T : Finset (Fin d)} (h : S ≠ T) :
    cubeDirectionResponse S T ≠ 0 := (cubeDirectionResponse_zero_iff S T).not.mpr h

end Hindman168
