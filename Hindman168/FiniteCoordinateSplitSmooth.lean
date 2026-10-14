import Hindman168.FiniteCoordinateSplit
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Hindman168

noncomputable def finiteCoordinateSplitContinuousLinearEquiv (m n : ℕ) :
    (Fin (m+n) → ℝ) ≃L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) := by
  let e : (Fin (m+n) → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) × (Fin n → ℝ) :=
    { finiteCoordinateSplitEquiv m n with
      map_add' := by intros; apply Prod.ext <;> funext i <;> rfl
      map_smul' := by intros; apply Prod.ext <;> funext i <;> rfl }
  exact e.toContinuousLinearEquiv

theorem finite_coordinate_split_continuous_apply (m n : ℕ) (x : Fin (m+n) → ℝ) :
    finiteCoordinateSplitContinuousLinearEquiv m n x = finiteCoordinateSplitEquiv m n x := rfl

theorem finite_coordinate_split_continuous_symm_apply (m n : ℕ)
    (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    (finiteCoordinateSplitContinuousLinearEquiv m n).symm x = Fin.append x.1 x.2 := rfl

end Hindman168
