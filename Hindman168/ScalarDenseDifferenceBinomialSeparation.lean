import Hindman168.ScalarDenseDifferenceSeparation
import Hindman168.ScalarBinomialCoefficientModOne

/-! BOTH monomial and paper-binomial higher nonlinear bounds with ONE
actual common multiplier, fixed before all source coefficients and samples. -/
namespace Hindman168
open Polynomial
open scoped Classical

theorem scalar_dense_difference_binomial_separation (D : ℕ) (δ A : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) :
    ∃ S T : ℕ, ∃ C : ℝ, 0 < S ∧ 0 < T ∧ 0 ≤ C ∧
      ∀ P Q : ℝ[X], Q.natDegree ≤ D → ∀ (σ : ℕ → ℝ) (N : ℕ), T ≤ N →
        ∀ U : Finset ℕ, U ⊆ Finset.range N → δ*(N : ℝ) ≤ U.card →
        (∀ h ∈ U, (N : ℝ)^2*‖((scalarDifferencePolynomial P Q h (σ h)).coeff 2 : UnitAddCircle)‖ ≤ A) →
        ∃ M : ℕ, 0 < M ∧ M ≤ S ∧
          (∀ j : ℕ, 3 ≤ j → j ≤ D →
            (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ C) ∧
          ∀ j : ℕ, 3 ≤ j → j ≤ D →
            (N : ℝ)^j*‖(((M : ℝ)*scalarPolynomialBinomialCoefficient Q D j : ℝ) : UnitAddCircle)‖ ≤ C := by
  obtain ⟨S,T,hS,hT,hInv⟩ := scalar_dense_difference_separation D δ A hδ hδ1 hA
  let C : ℝ := (scalarBinomialCoefficientBudget D : ℝ)*(S : ℝ)*A
  have hBudget : (1 : ℝ) ≤ scalarBinomialCoefficientBudget D := by
    exact_mod_cast scalar_binomial_coefficient_budget_positive D
  have hSA : 0 ≤ (S : ℝ)*A := mul_nonneg (Nat.cast_nonneg S) hA
  have hC : (S : ℝ)*A ≤ C := by dsimp [C]; nlinarith
  refine ⟨S,T,C,hS,hT,by dsimp [C]; positivity,?_⟩
  intro P Q hQ σ N hTN U hU hdense hcoeff
  obtain ⟨M,hM,hMS,hHigher⟩ := hInv P Q hQ σ N hTN U hU hdense hcoeff
  refine ⟨M,hM,hMS,fun j hj hjD => (hHigher j hj hjD).trans hC,?_⟩
  intro j hj hjD
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hT.trans_le hTN
  simpa only [C,mul_assoc] using
    scalar_binomial_coefficient_mod_one Q D M j 3 hjD hj (N : ℝ) ((S : ℝ)*A) hN hSA hHigher

end Hindman168
