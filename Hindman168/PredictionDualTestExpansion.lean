import Hindman168.VariableCubeReplicaLaw
import Hindman168.FiniteReplicaConditioning

/-!
# Exact product expansion for the actual finite dual cube formula

Each replica has its own dimension, original prime law, prime-dependent
shift length and modulus, and bounded prime-only factor. The common root
is sampled once. The finite identity retains every original coefficient;
conditioned good-tuple laws can also be substituted without approximation.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionReplicaDualTest {b : ℕ} (dim : Fin b → ℕ)
    {α : Fin b → Type*} (μ : ∀ q, Mass (α q))
    (A : ∀ q, α q → Fin (dim q) × Bool → ℤ) (T : ∀ q, α q → ℕ)
    (M : ∀ q, α q → ℤ) (e : ∀ q, α q → ℝ)
    (g : ∀ q, α q → CubeVertex (dim q) → ℤ → ℝ) (q : Fin b) (y : ℤ) : ℝ :=
  expectation (μ q) (fun x => expectation
    (piMass (fun jb => uniformIntervalMass (A q x jb) (T q x)))
    (fun u => e q x * ∏ S : CubeVertex (dim q),
      g q x S (y + M q x * ∑ j ∈ S.val, (u (j, true) - u (j, false)))))

def predictionReplicaColumnLocations {b : ℕ} {dim : Fin b → ℕ}
    {α : Fin b → Type*} (A : ∀ q, α q → Fin (dim q) × Bool → ℤ)
    (x : ∀ q, α q) : VariableReplicaCubeColumn dim → ℤ
  | none => 0
  | some ⟨q, jb⟩ => A q (x q) jb

def predictionReplicaRowTests {b : ℕ} {dim : Fin b → ℕ}
    {α : Fin b → Type*} (H : ℤ → ℝ)
    (g : ∀ q, α q → CubeVertex (dim q) → ℤ → ℝ) (x : ∀ q, α q) :
    VariableReplicaCubeRow dim → ℤ → ℝ
  | none => H
  | some ⟨q, S⟩ => g q (x q) S

theorem prediction_dual_product_cube_expansion {b : ℕ} (dim : Fin b → ℕ)
    {α : Fin b → Type*} (μ : ∀ q, Mass (α q)) (X W : ℕ) (H : ℤ → ℝ)
    (A : ∀ q, α q → Fin (dim q) × Bool → ℤ) (T : ∀ q, α q → ℕ)
    (M : ∀ q, α q → ℤ) (e : ∀ q, α q → ℝ)
    (g : ∀ q, α q → CubeVertex (dim q) → ℤ → ℝ) :
    expectation (integerMass X W) (fun y => H y * ∏ q, predictionReplicaDualTest dim μ A T M e g q y) =
      expectation (piMass μ) (fun x => expectation (piMass
        (variablePredictionOriginalColumnMass X W (predictionReplicaColumnLocations A x)
          (fun q => T q (x q))))
        (fun z => (∏ q, e q (x q)) * ∏ row, predictionReplicaRowTests H g x row
          (variableReplicaCubeEval (fun q => M q (x q)) row z))) := by
  unfold predictionReplicaDualTest
  rw [independent_replicas_root_product]
  apply congrArg (expectation (piMass μ))
  funext x
  rw [variable_cube_original_expectation_split, expectation_comm]
  apply congrArg (expectation (integerMass X W))
  funext y
  apply congrArg (expectation (piMass (fun q => piMass
    (fun jb => uniformIntervalMass (A q (x q) jb) (T q (x q))))))
  funext u
  rw [variable_cube_grouped_row_product, Finset.prod_mul_distrib]
  dsimp only [predictionReplicaRowTests]
  ring

theorem prediction_replica_prime_factor_bound {b : ℕ} {α : Fin b → Type*}
    (e : ∀ q, α q → ℝ) (he : ∀ q x, |e q x| ≤ 1) (x : ∀ q, α q) :
    |∏ q, e q (x q)| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _q : Fin b, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun q _ => he q (x q))
    _ = 1 := Finset.prod_const_one

theorem prediction_conditioned_dual_product_cube_expansion {b : ℕ} (dim : Fin b → ℕ)
    {α : Fin b → Type*} (μ : ∀ q, Mass (α q)) (E : ∀ q, α q → Prop)
    (X W : ℕ) (H : ℤ → ℝ)
    (A : ∀ q, α q → Fin (dim q) × Bool → ℤ) (T : ∀ q, α q → ℕ)
    (M : ∀ q, α q → ℤ) (e : ∀ q, α q → ℝ)
    (g : ∀ q, α q → CubeVertex (dim q) → ℤ → ℝ) :
    expectation (integerMass X W) (fun y => H y * ∏ q, predictionReplicaDualTest dim
      (fun q => conditionMass (μ q) (E q)) A T M e g q y) =
      expectation (piMass μ) (fun x => if ∀ q, E q (x q) then expectation (piMass
        (variablePredictionOriginalColumnMass X W (predictionReplicaColumnLocations A x)
          (fun q => T q (x q))))
        (fun z => (∏ q, e q (x q)) * ∏ row, predictionReplicaRowTests H g x row
          (variableReplicaCubeEval (fun q => M q (x q)) row z)) else 0) /
        ∏ q, event (μ q) (E q) := by
  rw [prediction_dual_product_cube_expansion]
  rw [expectation_piMass_conditionMass]
  congr 1
  apply congrArg (expectation (piMass μ))
  funext x
  split_ifs <;> rfl

end Hindman168
