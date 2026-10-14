import Hindman168.VariableCubeReplicaLaw
import Mathlib.Data.Fintype.Powerset

/-!
# Exact constant-dimension original cube transport and vertex counts

Dependent replica coordinates are reindexed without changing any finite
mass. Nonempty cube vertices number exactly two to the dimension minus one.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def constantCubeColumnEquiv (b d : ℕ) :
    VariableReplicaCubeColumn (fun _ : Fin b => d) ≃ ReplicaCubeColumn b d where
  toFun c := match c with | none => none | some ⟨q, jb⟩ => some (q, jb)
  invFun c := match c with | none => none | some (q, jb) => some ⟨q, jb⟩
  left_inv c := by cases c with | none => rfl | some c => cases c; rfl
  right_inv c := by cases c with | none => rfl | some c => cases c; rfl

def constantCubeRowEquiv (b d : ℕ) :
    VariableReplicaCubeRow (fun _ : Fin b => d) ≃ ReplicaCubeRow b d where
  toFun c := match c with | none => none | some ⟨q, S⟩ => some (q, S)
  invFun c := match c with | none => none | some (q, S) => some ⟨q, S⟩
  left_inv c := by cases c with | none => rfl | some c => cases c; rfl
  right_inv c := by cases c with | none => rfl | some c => cases c; rfl

theorem constant_cube_evaluation {b d : ℕ} (M : Fin b → ℤ)
    (r : VariableReplicaCubeRow (fun _ : Fin b => d)) (z : ReplicaCubeColumn b d → ℤ) :
    variableReplicaCubeEval M r (fun c => z (constantCubeColumnEquiv b d c)) =
      replicaCubeEval M (constantCubeRowEquiv b d r) z := by
  cases r with
  | none => exact (replicaCubeEval_root M z).symm
  | some r => cases r; exact (replicaCubeEval_vertex M _ _ z).symm

theorem constant_cube_original_expectation {b d : ℕ} (X W : ℕ)
    (A : Fin b × Fin d × Bool → ℤ) (T : Fin b → ℕ)
    (f : (VariableReplicaCubeColumn (fun _ : Fin b => d) → ℤ) → ℝ) :
    expectation (piMass (variablePredictionOriginalColumnMass X W
      (fun c => match c with | none => 0 | some ⟨q, jb⟩ => A (q, jb)) T)) f =
    expectation (piMass (predictionOriginalColumnMass X W A T))
      (fun z => f (fun c => z (constantCubeColumnEquiv b d c))) := by
  have hcol : (fun c => variablePredictionOriginalColumnMass X W
      (fun c => match c with | none => 0 | some ⟨q, jb⟩ => A (q, jb)) T c) =
      (fun c => predictionOriginalColumnMass X W A T (constantCubeColumnEquiv b d c)) := by
    funext c
    cases c with | none => rfl | some c => cases c; rfl
  change expectation (piMass (fun c => variablePredictionOriginalColumnMass X W
    (fun c => match c with | none => 0 | some ⟨q, jb⟩ => A (q, jb)) T c)) f = _
  rw [hcol, ← piMass_reindex, expectation_push]

theorem constant_cube_row_product {b d : ℕ} (M : Fin b → ℤ)
    (ν : ℤ → ℝ) (z : ReplicaCubeColumn b d → ℤ) :
    (∏ r : VariableReplicaCubeRow (fun _ : Fin b => d),
      (1 + ν (variableReplicaCubeEval M r (fun c => z (constantCubeColumnEquiv b d c))))) =
    ∏ r : ReplicaCubeRow b d, (1 + ν (replicaCubeEval M r z)) := by
  simp_rw [constant_cube_evaluation]
  exact Fintype.prod_equiv (constantCubeRowEquiv b d) _ _ (fun _ => rfl)

theorem constant_cube_majorant_expectation {b d : ℕ} (X W : ℕ)
    (T : Fin b → ℕ) (M : Fin b → ℤ) (ν : ℤ → ℝ) :
    expectation (piMass (variablePredictionOriginalColumnMass X W
      (fun _ : VariableReplicaCubeColumn (fun _ : Fin b => d) => 0) T))
      (fun z => ∏ row : VariableReplicaCubeRow (fun _ : Fin b => d),
        (1 + ν (variableReplicaCubeEval M row z))) =
    expectation (piMass (predictionOriginalColumnMass X W (fun _ => 0) T))
      (fun z => ∏ row : ReplicaCubeRow b d, (1 + ν (replicaCubeEval M row z))) := by
  have hlaw : piMass (variablePredictionOriginalColumnMass X W
      (fun _ : VariableReplicaCubeColumn (fun _ : Fin b => d) => 0) T) =
      (piMass (predictionOriginalColumnMass X W (fun _ : Fin b × Fin d × Bool => 0) T)).mapDomain
        (fun z c => z (constantCubeColumnEquiv b d c)) := by
    rw [piMass_reindex]
    congr 1
    funext c
    cases c with | none => rfl | some c => cases c; rfl
  rw [hlaw, expectation_push]
  apply congrArg (expectation (piMass (predictionOriginalColumnMass X W (fun _ => 0) T)))
  funext z
  exact constant_cube_row_product M ν z

theorem cubeVertex_card (d : ℕ) : Fintype.card (CubeVertex d) = 2 ^ d - 1 := by
  have he : (CubeVertex d) ≃ {S : Finset (Fin d) // S ≠ ∅} :=
    Equiv.subtypeEquivRight (fun _ => Finset.nonempty_iff_ne_empty)
  rw [Fintype.card_congr he, Fintype.card_subtype_compl (fun S : Finset (Fin d) => S = ∅)]
  simp only [Fintype.card_subtype_eq, Fintype.card_finset, Fintype.card_fin]

theorem replicaCubeRow_card (b d : ℕ) :
    Fintype.card (ReplicaCubeRow b d) = 1 + b * (2 ^ d - 1) := by
  simp only [ReplicaCubeRow, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, cubeVertex_card]
  omega

end Hindman168
