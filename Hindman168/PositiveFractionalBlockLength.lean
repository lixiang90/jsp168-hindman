import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace Hindman168

theorem positive_fractional_floor_length (ρ : ℝ) (N : ℕ)
    (hlarge : 2 ≤ ρ*(N : ℝ)) :
    0 < ⌊ρ*(N : ℝ)⌋₊ ∧ ρ*(N : ℝ)/2 ≤ (⌊ρ*(N : ℝ)⌋₊ : ℝ) ∧
      (⌊ρ*(N : ℝ)⌋₊ : ℝ) ≤ ρ*(N : ℝ) := by
  have hl := Nat.lt_floor_add_one (ρ*(N : ℝ))
  have hu := Nat.floor_le (by positivity : 0 ≤ ρ*(N : ℝ))
  have hp : (0 : ℝ) < ⌊ρ*(N : ℝ)⌋₊ := by linarith
  exact ⟨by exact_mod_cast hp, by linarith, hu⟩

end Hindman168

