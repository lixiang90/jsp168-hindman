import Hindman168.ScalarBinomialCoefficientModOne
import Hindman168.UnitCirclePolynomialInverse
import Hindman168.PolynomialSmallValuesInverse

namespace Hindman168
open Polynomial
open scoped Classical

/-- The genuine arbitrary-observable circle inverse in the binomial basis. -/
theorem scalar_binomial_polynomial_observable_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, 0 < N →
      ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCirclePolynomialDiscrepancy p N F‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ i : ℕ, 0 < i → i ≤ D →
          (N : ℝ)^i*‖(((q : ℝ)*scalarPolynomialBinomialCoefficient p D i : ℝ) :
            UnitAddCircle)‖ ≤ (B : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_polynomial_inverse D δ hδ
  let B := scalarBinomialCoefficientBudget D*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (scalarBinomialCoefficientBudget D : ℝ)*(A : ℝ) ≤ B := by
    exact_mod_cast (Nat.le_add_right (scalarBinomialCoefficientBudget D*A) A)
  refine ⟨B, hB, ?_⟩
  intro p hp N hN F hF hdiscrepancy
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv p hp N hN F hF hdiscrepancy
  refine ⟨q, hq, hqA.trans hAB, ?_⟩
  intro i hi hiD
  exact (scalar_binomial_coefficient_mod_one p D q i 1 hiD hi (N : ℝ) (A : ℝ)
    (by exact_mod_cast hN) (by positivity)
    (fun j hj hjD => hcoeff j hj hjD)).trans hbudget

/-- Actual dense small values yield one multiplier for ALL binomial
coefficients, including constant and zero tolerance, on the original large box. -/
theorem scalar_binomial_polynomial_small_values_inverse (D : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, B ≤ N →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ/10 →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ i : ℕ, i ≤ D →
          (N : ℝ)^i*‖(((q : ℝ)*scalarPolynomialBinomialCoefficient p D i : ℝ) :
            UnitAddCircle)‖ ≤ (B : ℝ)*ε := by
  obtain ⟨A, hA, hinv⟩ := polynomial_small_values_inverse D δ hδ hδ1
  let B := scalarBinomialCoefficientBudget D*A+A
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  have hbudget : (scalarBinomialCoefficientBudget D : ℝ)*(A : ℝ) ≤ B := by
    exact_mod_cast (Nat.le_add_right (scalarBinomialCoefficientBudget D*A) A)
  refine ⟨B, hB, ?_⟩
  intro p hp N hBN ε hε hεsmall hdense
  have hAN := hAB.trans hBN
  have hN : 0 < N := hA.trans_le hAN
  obtain ⟨q, hq, hqA, hcoeff⟩ := hinv p hp N hAN ε hε hεsmall hdense
  refine ⟨q, hq, hqA.trans hAB, ?_⟩
  intro i hi
  have h := scalar_binomial_coefficient_mod_one p D q i 0 hi (Nat.zero_le i)
    (N : ℝ) ((A : ℝ)*ε) (by exact_mod_cast hN) (by positivity)
    (fun j _ hjD => hcoeff j hjD)
  calc
    _ ≤ (scalarBinomialCoefficientBudget D : ℝ)*((A : ℝ)*ε) := h
    _ = ((scalarBinomialCoefficientBudget D : ℝ)*(A : ℝ))*ε := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hε

end Hindman168
