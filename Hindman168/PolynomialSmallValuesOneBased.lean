import Hindman168.ScalarPolynomialUnitShift
import Hindman168.PolynomialSmallValuesInverse

namespace Hindman168
open Polynomial
open scoped Classical

/-- The actual one-based auxiliary convention {1,...,N}. The same bounded
multiplier controls all ORIGINAL coefficients after true integer translation,
including the constant and epsilon=0. The large-N hypothesis is retained. -/
theorem polynomial_small_values_one_based_inverse (D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, B ≤ N →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ/10 →
        δ*(N : ℝ) ≤ ((Finset.Icc 1 N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ i : ℕ, i ≤ D →
          (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε := by
  obtain ⟨A, hA, hinv⟩ := polynomial_small_values_inverse D δ hδ hδ1
  let B := (D+1)*2^D*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (D+1 : ℕ)*(2 : ℝ)^D*(A : ℝ) ≤ B := by
    exact_mod_cast (Nat.le_add_right ((D+1)*2^D*A) A)
  refine ⟨B, hB, ?_⟩
  intro p hp N hBN ε hε hεsmall hdense
  have hAN := hAB.trans hBN
  have hN : 0 < N := hA.trans_le hAN
  let r := scalarPolynomialOnProgression p 1 1
  have hr : r.natDegree ≤ D := scalar_polynomial_on_progression_degree p 1 1 D hp
  have hev (n : ℕ) : r.eval (n : ℝ) = p.eval ((n+1 : ℕ) : ℝ) := by
    dsimp only [r]
    rw [scalar_polynomial_on_progression_eval]
    congr 1
    push_cast
    ring
  have hd : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
      ‖((r.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card := by
    simp_rw [hev]
    rw [scalar_polynomial_one_based_small_values_card]
    exact hdense
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv r hr N hAN ε hε hεsmall hd
  refine ⟨q, hq, hqA.trans hAB, ?_⟩
  intro i _
  have h := scalar_polynomial_unit_shift_recovery p D q i hp (N : ℝ) ((A : ℝ)*ε)
    (by exact_mod_cast hN) (by positivity) hcoeff
  calc
    _ ≤ (D+1 : ℕ)*(2 : ℝ)^D*((A : ℝ)*ε) := h
    _ = ((D+1 : ℕ)*(2 : ℝ)^D*(A : ℝ))*ε := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hε

end Hindman168
