import Hindman168.VariableCubePadding
import Hindman168.FiniteReplicaJointLaw

/-!
# Exact original column law grouped into variable-dimensional replicas

The single harmonic root is separated from the original per-replica shift
blocks. The equivalence preserves every coefficient, even before interval
or harmonic normalization. No common replica dimension is required.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

abbrev VariableCubeShifts {b : ℕ} (dim : Fin b → ℕ) :=
  ∀ q, Fin (dim q) × Bool → ℤ

def variableCubeCoordinates {b : ℕ} {dim : Fin b → ℕ} (y : ℤ)
    (u : VariableCubeShifts dim) : VariableReplicaCubeColumn dim → ℤ
  | none => y
  | some ⟨q, j, bit⟩ => u q (j, bit)

def variableCubeSampleEquiv {b : ℕ} (dim : Fin b → ℕ) :
    (VariableReplicaCubeColumn dim → ℤ) ≃ (ℤ × VariableCubeShifts dim) where
  toFun z := (z none, fun q jb => z (some ⟨q, jb⟩))
  invFun p := variableCubeCoordinates p.1 p.2
  left_inv z := by
    funext col
    cases col with
    | none => rfl
    | some c => cases c; rfl
  right_inv p := by cases p; rfl

noncomputable def variableReplicaShiftMass {b : ℕ} {dim : Fin b → ℕ}
    (A : VariableReplicaCubeColumn dim → ℤ) (T : Fin b → ℕ) (q : Fin b) :
    Mass (Fin (dim q) × Bool → ℤ) :=
  piMass (fun jb => uniformIntervalMass (A (some ⟨q, jb⟩)) (T q))

theorem variable_cube_original_law_split {b : ℕ} {dim : Fin b → ℕ}
    (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ) (T : Fin b → ℕ) :
    (piMass (variablePredictionOriginalColumnMass X W A T)).mapDomain
      (variableCubeSampleEquiv dim) =
      tensor (integerMass X W) (piMass (variableReplicaShiftMass A T)) := by
  ext p
  rw [Finsupp.mapDomain_equiv_apply, piMass_apply, tensor_apply]
  simp only [Fintype.prod_option, piMass_apply, variableReplicaShiftMass,
    variablePredictionOriginalColumnMass, variableCubeSampleEquiv]
  congr 1
  exact Fintype.prod_sigma _

theorem variable_cube_original_expectation_split {b : ℕ} {dim : Fin b → ℕ}
    (X W : ℕ) (A : VariableReplicaCubeColumn dim → ℤ) (T : Fin b → ℕ)
    (f : (VariableReplicaCubeColumn dim → ℤ) → ℝ) :
    expectation (piMass (variablePredictionOriginalColumnMass X W A T)) f =
      expectation (integerMass X W) (fun y => expectation (piMass (variableReplicaShiftMass A T))
        (fun u => f (variableCubeCoordinates y u))) := by
  have h := congrArg (fun μ => expectation μ
    (fun p => f ((variableCubeSampleEquiv dim).symm p))) (variable_cube_original_law_split X W A T)
  simp only [expectation_push, Equiv.symm_apply_apply, expectation_tensor] at h
  exact h

theorem variable_cube_grouped_row_product {b : ℕ} {dim : Fin b → ℕ}
    (M : Fin b → ℤ) (G : VariableReplicaCubeRow dim → ℤ → ℝ)
    (y : ℤ) (u : VariableCubeShifts dim) :
    (∏ row, G row (variableReplicaCubeEval M row (variableCubeCoordinates y u))) =
      G none y * ∏ q, ∏ S : CubeVertex (dim q),
        G (some ⟨q, S⟩) (y + M q * ∑ j ∈ S.val, (u q (j, true) - u q (j, false))) := by
  rw [Fintype.prod_option]
  simp only [variableReplicaCubeEval, variableCubeCoordinates]
  congr 1
  exact Fintype.prod_sigma _

end Hindman168
