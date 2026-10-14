import Hindman168.MasterNormalizedDualProductLimit

/-! Empty independent coordinates retain exactly one unit coefficient. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem piMass_empty_expectation {ι : Type*} [Fintype ι] [IsEmpty ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (f : (∀ i, α i) → ℝ) :
    expectation (piMass μ) f = f (fun i => isEmptyElim i) := by
  have hf : f = (fun _ => f (fun i => isEmptyElim i)) := by
    funext x
    apply congrArg f
    funext i
    exact isEmptyElim i
  rw [hf, expectation_const, piMass_total]
  simp

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem variable_cube_empty_root_average (dim : Fin 0 → ℕ) (X W : ℕ)
    (A : VariableReplicaCubeColumn dim → ℤ) (T : Fin 0 → ℕ) (H : ℤ → ℝ) :
    expectation (piMass (variablePredictionOriginalColumnMass X W A T)) (fun z => H (z none)) =
      expectation (integerMass X W) H := by
  rw [variable_cube_original_expectation_split]
  simp only [piMass_empty_expectation, variableCubeCoordinates]

theorem variable_cube_empty_row_product (dim : Fin 0 → ℕ)
    (M : Fin 0 → ℤ) (G : VariableReplicaCubeRow dim → ℤ → ℝ)
    (z : VariableReplicaCubeColumn dim → ℤ) :
    (∏ row, G row (variableReplicaCubeEval M row z)) = G none (z none) := by
  rw [Fintype.prod_option]
  simp [variableReplicaCubeEval]

end Hindman168
