import Hindman168.MasterPredictionVariableQuotientLimit
import Hindman168.PredictionDualTestExpansion

/-!
# Disjoint local prime slots and their exact original master law

Each replica may have a different prime arity, including zero. A bijection
from the disjoint union to the global slots retains all independent draw
coefficients, even when replicas use the same gap. Polynomial renaming uses
only the corresponding replica slots, so the sparse gap condition is proved.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def replicaPrimeSlot {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (q : Fin b) (j : Fin (arity q)) : Fin r :=
  e ⟨q, j⟩

theorem replicaPrimeSlot_injective {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (q : Fin b) : Function.Injective (replicaPrimeSlot e q) := by
  intro j k h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2

def replicaPrimeSampleEquiv {b r : ℕ} (arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r) :
    (Fin r → ℕ) ≃ (∀ q, Fin (arity q) → ℕ) where
  toFun x q j := x (replicaPrimeSlot e q j)
  invFun x j := x (e.symm j).1 (e.symm j).2
  left_inv x := by
    funext j
    simp only [replicaPrimeSlot, Sigma.eta, Equiv.apply_symm_apply]
  right_inv x := by
    funext q j
    exact congrArg (fun v : Σ q, Fin (arity q) => x v.1 v.2) (e.symm_apply_apply ⟨q, j⟩)

def replicaPrimeGap {b r N : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (gap : Fin b → Fin N) (j : Fin r) : Fin N :=
  gap (e.symm j).1

theorem replicaPrimeGap_slot {b r N : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (gap : Fin b → Fin N)
    (q : Fin b) (j : Fin (arity q)) : replicaPrimeGap e gap (replicaPrimeSlot e q j) = gap q := by
  simp only [replicaPrimeGap, replicaPrimeSlot, Equiv.symm_apply_apply]

theorem master_replica_prime_law {b r N : ℕ} (arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin b → Fin N) :
    (masterPrimeSlotsMass F w (fun j => replicaPrimeGap e gap j)).mapDomain
      (replicaPrimeSampleEquiv arity e) =
      piMass (fun q => primeIndependentMass (arity q) (F.pool w (gap q)).lower (F.pool w (gap q)).upper) := by
  ext x
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [masterPrimeSlotsMass, primeIndependentMass, piMass_apply]
  calc
    _ = ∏ p : (Σ q, Fin (arity q)),
        primePoolMass (F.pool w (gap p.1)).lower (F.pool w (gap p.1)).upper (x p.1 p.2) :=
      Fintype.prod_equiv e.symm _ _ (fun j => rfl)
    _ = _ := Fintype.prod_sigma _

theorem master_replica_prime_expectation {b r N : ℕ} (arity : Fin b → ℕ)
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (F : MasterParameterFamily) (w : ℕ)
    (gap : Fin b → Fin N) (f : (∀ q, Fin (arity q) → ℕ) → ℝ) :
    expectation (masterPrimeSlotsMass F w (fun j => replicaPrimeGap e gap j))
      (fun x => f ((replicaPrimeSampleEquiv arity e) x)) =
      expectation (piMass (fun q => primeIndependentMass (arity q)
        (F.pool w (gap q)).lower (F.pool w (gap q)).upper)) f := by
  rw [← master_replica_prime_law arity e F w gap, expectation_push]

noncomputable def replicaPolynomialLift {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (q : Fin b)
    (f : MvPolynomial (Fin (arity q)) ℤ) : MvPolynomial (Fin r) ℤ :=
  MvPolynomial.rename (replicaPrimeSlot e q) f

theorem replicaPolynomialLift_eval {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (q : Fin b)
    (f : MvPolynomial (Fin (arity q)) ℤ) (x : Fin r → ℕ) :
    MvPolynomial.eval (fun j => (x j : ℤ)) (replicaPolynomialLift e q f) =
      MvPolynomial.eval (fun j => (((replicaPrimeSampleEquiv arity e) x q j) : ℤ)) f := by
  exact MvPolynomial.eval_rename (replicaPrimeSlot e q) (fun j => (x j : ℤ)) f

theorem replicaPolynomialLift_nonzero {b r : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (q : Fin b)
    (f : MvPolynomial (Fin (arity q)) ℤ) (hf : f ≠ 0) : replicaPolynomialLift e q f ≠ 0 := by
  exact fun h => hf ((MvPolynomial.rename_eq_zero_iff_of_injective f (replicaPrimeSlot_injective e q)).mp h)

theorem replicaPolynomialLift_vars_gap {b r N : ℕ} {arity : Fin b → ℕ}
    (e : (Σ q, Fin (arity q)) ≃ Fin r) (gap : Fin b → Fin N) (q : Fin b)
    (f : MvPolynomial (Fin (arity q)) ℤ) (j : Fin r)
    (hj : j ∈ (replicaPolynomialLift e q f).vars) : replicaPrimeGap e gap j = gap q := by
  obtain ⟨k, _, hk⟩ := MvPolynomial.mem_vars_rename (replicaPrimeSlot e q) f hj
  rw [← hk]
  exact replicaPrimeGap_slot e gap q k

end Hindman168
