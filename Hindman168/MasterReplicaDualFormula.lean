import Hindman168.MasterLocalGoodTupleLaw

/-!
# Exact normalized local dual formula and global cube numerator

The local prime law is the original reciprocal-prime law conditioned on
its precise local good event. Each replica retains its own prime arity,
dimension, denominator, gap and finite J choice. Exact slot transport
identifies the numerator with the actual master weighted cube average.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def masterReplicaLocalPrimeMass {b N : ℕ} (F : MasterParameterFamily)
    (arity : Fin b → ℕ) (gap : ℕ → Fin b → Fin N) (w : ℕ) (q : Fin b) :
    Mass (Fin (arity q) → ℕ) :=
  primeIndependentMass (arity q) (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper

noncomputable def masterReplicaLocalModulus {b : ℕ} {arity : Fin b → ℕ}
    (F : MasterParameterFamily) (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ)
    (w : ℕ) (q : Fin b) (x : Fin (arity q) → ℕ) : ℤ :=
  predictionCubeModulus w (F.modulus w : ℕ) (den q) x

noncomputable def masterReplicaLocalLength {b N K : ℕ} {arity : Fin b → ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin b → Fin N) (J : Fin K → ℕ)
    (choice : ℕ → Fin b → Fin K) (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ)
    (w : ℕ) (q : Fin b) (x : Fin (arity q) → ℕ) : ℕ :=
  F.gap w (gap w q).val / (J (choice w q) * (masterReplicaLocalModulus F den w q x).natAbs)

noncomputable def masterReplicaGoodDualTest {b N K : ℕ} (F : MasterParameterFamily)
    (dim arity : Fin b → ℕ) (gap : ℕ → Fin b → Fin N)
    (J : Fin K → ℕ) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ)
    (w : ℕ) (q : Fin b) (y : ℤ) : ℝ :=
  predictionReplicaDualTest dim (fun q => conditionMass (masterReplicaLocalPrimeMass F arity gap w q)
    (predictionLocalPrimeGoodEvent F (tests q) (den q) w)) (fun _ _ _ => 0)
    (masterReplicaLocalLength F gap J choice den w) (masterReplicaLocalModulus F den w) (ε w) (g w) q y

noncomputable def masterReplicaDualNumerator {b r N K : ℕ} (F : MasterParameterFamily)
    (root : ℕ → Fin N) (dim arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (gap : ℕ → Fin b → Fin N)
    (J : Fin K → ℕ) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (H : ℕ → ℤ → ℝ)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ) : ℕ → ℝ :=
  masterPredictionVariableWeightedCubeAverage F root (fun w j => replicaPrimeGap e (gap w) j)
    (fun w _ => (F.modulus w : ℕ)) (fun q => replicaPolynomialLift e q (den q)) (fun _ _ _ => 0)
    (predictionVariableQuotientLength F gap J choice (fun w _ => (F.modulus w : ℕ))
      (fun q => replicaPolynomialLift e q (den q)))
    (fun w x => ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w ((replicaPrimeSampleEquiv arity e) x q))
    (fun w x => predictionReplicaRowTests (H w) (g w) ((replicaPrimeSampleEquiv arity e) x))
    (fun w x => ∏ q, ε w q ((replicaPrimeSampleEquiv arity e) x q))

theorem masterReplicaLocalModulus_lift {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (F : MasterParameterFamily)
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (w : ℕ) (q : Fin b) (x : Fin r → ℕ) :
    predictionCubeModulus w (F.modulus w : ℕ) (replicaPolynomialLift e q (den q)) x =
      masterReplicaLocalModulus F den w q ((replicaPrimeSampleEquiv arity e) x q) := by
  unfold predictionCubeModulus masterReplicaLocalModulus
  rw [replicaPolynomialLift_eval]
  rfl

theorem masterReplicaLocalLength_lift {b r N K : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (F : MasterParameterFamily)
    (gap : ℕ → Fin b → Fin N) (J : Fin K → ℕ) (choice : ℕ → Fin b → Fin K)
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (w : ℕ) (q : Fin b) (x : Fin r → ℕ) :
    predictionVariableQuotientLength F gap J choice (fun w _ => (F.modulus w : ℕ))
      (fun q => replicaPolynomialLift e q (den q)) w x q =
      masterReplicaLocalLength F gap J choice den w q ((replicaPrimeSampleEquiv arity e) x q) := by
  unfold predictionVariableQuotientLength predictionQuotientLength masterReplicaLocalLength
  rw [masterReplicaLocalModulus_lift]

theorem master_replica_dual_normalized_formula {b r N K : ℕ} (F : MasterParameterFamily)
    (root : ℕ → Fin N) (dim arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (gap : ℕ → Fin b → Fin N)
    (J : Fin K → ℕ) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (H : ℕ → ℤ → ℝ)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ) (w : ℕ) :
    expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => H w y * ∏ q, masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y) =
      masterReplicaDualNumerator F root dim arity e gap J choice tests den H ε g w /
        ∏ q, event (masterReplicaLocalPrimeMass F arity gap w q)
          (predictionLocalPrimeGoodEvent F (tests q) (den q) w) := by
  unfold masterReplicaGoodDualTest
  rw [prediction_conditioned_dual_product_cube_expansion]
  congr 1
  let f (x : ∀ q, Fin (arity q) → ℕ) := if ∀ q, predictionLocalPrimeGoodEvent F (tests q) (den q) w (x q) then
    expectation (piMass (variablePredictionOriginalColumnMass (F.cutoff w (root w).val) (primorial w)
      (predictionReplicaColumnLocations (fun _ _ _ => 0) x) (fun q => masterReplicaLocalLength F gap J choice den w q (x q))))
      (fun z => (∏ q, ε w q (x q)) * ∏ row, predictionReplicaRowTests (H w) (g w) x row
        (variableReplicaCubeEval (fun q => masterReplicaLocalModulus F den w q (x q)) row z)) else 0
  have hp := master_replica_prime_expectation arity e F w (gap w) f
  unfold masterReplicaDualNumerator masterPredictionVariableWeightedCubeAverage
  calc
    _ = expectation (piMass (fun q => primeIndependentMass (arity q)
        (F.pool w (gap w q)).lower (F.pool w (gap w q)).upper)) f := by
      apply congrArg (expectation (piMass (masterReplicaLocalPrimeMass F arity gap w)))
      funext x
      rfl
    _ = expectation (masterPrimeSlotsMass F w (fun j => replicaPrimeGap e (gap w) j))
        (fun x => f ((replicaPrimeSampleEquiv arity e) x)) := hp.symm
    _ = _ := by
      apply congrArg (expectation (masterPrimeSlotsMass F w (fun j => replicaPrimeGap e (gap w) j)))
      funext x
      dsimp only [f]
      split_ifs
      · have hT : predictionVariableQuotientLength F gap J choice (fun w _ => (F.modulus w : ℕ))
            (fun q => replicaPolynomialLift e q (den q)) w x =
            (fun q => masterReplicaLocalLength F gap J choice den w q ((replicaPrimeSampleEquiv arity e) x q)) := by
          funext q
          exact masterReplicaLocalLength_lift e F gap J choice den w q x
        have hA : predictionReplicaColumnLocations (fun _ _ _ => 0) ((replicaPrimeSampleEquiv arity e) x) =
            (fun _ : VariableReplicaCubeColumn dim => (0 : ℤ)) := by
          funext col
          cases col <;> rfl
        rw [hA, ← hT]
        simp only [masterReplicaLocalModulus_lift]
      · rfl

end Hindman168
