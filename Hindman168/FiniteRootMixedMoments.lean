import Hindman168.FiniteWeightedCauchySchwarz

/-! Exact integration of one or two independent retained root factors.
The first identity uses the unused root law's actual normalization. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem expectation_unused_root_weight {α : Type*} (μ : Mass α)
    (hμ : total μ = 1) (c : ℝ) (f : α → ℝ) :
    expectation μ (fun u => expectation μ (fun _v => c * f u)) = c * expectation μ f := by
  simp only [expectation_const, hμ, one_mul]
  exact expectation_const_mul μ c f

theorem expectation_root_weighted_square {α : Type*} (μ : Mass α)
    (c : ℝ) (f : α → ℝ) :
    expectation μ (fun u => expectation μ (fun v => c * f u * f v)) = c * (expectation μ f) ^ 2 := by
  calc
    _ = expectation (tensor μ μ) (fun uv => c * (f uv.1 * f uv.2)) := by
      rw [expectation_tensor]
      apply congrArg (expectation μ)
      funext u
      apply congrArg (expectation μ)
      funext v
      ring
    _ = _ := by rw [expectation_const_mul, expectation_independent_square]

end Hindman168.FiniteMass
