import Mathlib.Data.Fin.Tuple.Basic

namespace Hindman168

variable {α : Type*}

def finiteCoordinateSplitEquiv (m n : ℕ) :
    (Fin (m+n) → α) ≃ (Fin m → α) × (Fin n → α) where
  toFun x := (fun i => x (Fin.castAdd n i), fun i => x (Fin.natAdd m i))
  invFun x := Fin.append x.1 x.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp only [Fin.append_left, Fin.append_right]

theorem finite_coordinate_split_predicate_iff (m n : ℕ) (P : α → Prop)
    (x : Fin (m+n) → α) :
    (∀ i, P (x i)) ↔
      (∀ i, P ((finiteCoordinateSplitEquiv m n x).1 i)) ∧
        (∀ i, P ((finiteCoordinateSplitEquiv m n x).2 i)) := by
  constructor
  · intro h
    exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨hL, hR⟩ i
    cases i using Fin.addCases with
    | left i => exact hL i
    | right i => exact hR i

end Hindman168
