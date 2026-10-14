import Hindman168.ScalarFractionalBracketFirstAlternative

/-! Actual mixed-frequency output yields the second small-slope bracket
input with correct coefficient/error budgets and nearest-integer residual. -/
namespace Hindman168
open scoped BigOperators

theorem scalar_mixed_fractional_bracket_reduction {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (r : ℤ) (k : ι → ℤ)
    (R Z A B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hr : |(r : ℝ)| ≤ R) (hk : ∀ i, |(k i : ℝ)| ≤ R) (hζ : ∀ i, |ζ i| ≤ Z)
    (N : ℕ) (hMixed : (N : ℝ)*‖(((∑ i, (k i : ℝ)*γ i)+(r : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ A) :
    let a := (r : ℝ)*α+∑ i, (k i : ℝ)*γ i
    (N : ℝ)*|scalarNearestIntegerResidual a| ≤ A ∧
      (∀ i, |(r : ℝ)*ζ i-(k i : ℝ)| ≤ R*(Z+1)) ∧
      ∀ h : ℕ, (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B →
        (N : ℝ)*‖(scalarFractionalBracket ((r : ℝ)*β) (scalarNearestIntegerResidual a)
          (fun i => (r : ℝ)*ζ i-(k i : ℝ)) γ (h : ℝ) : UnitAddCircle)‖ ≤ R*B := by
  intro a
  refine ⟨?_,?_,?_⟩
  · rw [scalar_nearest_integer_residual_abs]
    have he : a=(∑ i, (k i : ℝ)*γ i)+(r : ℝ)*α := by dsimp only [a]; ring
    rw [he]
    exact hMixed
  · intro i
    have hm : |(r : ℝ)*ζ i| ≤ R*Z := by
      rw [abs_mul]
      exact mul_le_mul hr (hζ i) (abs_nonneg _) hR
    exact ((abs_sub _ _).trans (add_le_add hm (hk i))).trans (by linarith)
  · intro h hsmall
    exact (scalar_fractional_bracket_corrected_error β α ζ γ r k h N B hsmall).trans
      (mul_le_mul_of_nonneg_right hr hB)

end Hindman168
