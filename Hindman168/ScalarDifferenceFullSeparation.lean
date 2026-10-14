import Hindman168.ScalarDifferencePaperLinearRelation

/-! Complete actual remaining scalar reconstruction under the PROVED higher
Q bounds, with the SAME multiplier and SAME useful shifts. -/
namespace Hindman168
open Polynomial
open scoped BigOperators Classical

theorem scalar_difference_full_separation (P Q : ℝ[X]) (D M S N : ℕ) (A B : ℝ)
    (hP : P.natDegree ≤ D) (hQ : Q.natDegree ≤ D) (hD : 2 ≤ D) (hZero : P.eval 0=0)
    (hMS : M ≤ S) (hN : 0 < N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (σ : ℕ → ℝ) (U : Finset ℕ) (hUne : U.Nonempty)
    (hU : ∀ h ∈ U, h ≤ N)
    (hR : ∀ h ∈ U, ∀ i : ℕ, 0 < i → i ≤ D →
      (N : ℝ)^i*‖((scalarDifferencePolynomial P Q h (σ h)).coeff i : UnitAddCircle)‖ ≤ A)
    (hHigherQ : ∀ j : ℕ, 3 ≤ j → j ≤ D →
      (N : ℝ)^j*‖(((M : ℝ)*Q.coeff j : ℝ) : UnitAddCircle)‖ ≤ B) :
    let C : ℝ := (S : ℝ)*A+(scalarTaylorTailBudget D : ℝ)*B
    (∀ i : ℕ, 2 ≤ i → i ≤ D →
      (N : ℝ)^i*‖(((M : ℝ)*P.coeff i : ℝ) : UnitAddCircle)‖ ≤ C) ∧
    (∀ i : ℕ, 2 ≤ i → i ≤ D →
      (N : ℝ)^i*‖(((M : ℝ)*scalarPolynomialBinomialCoefficient P D i : ℝ) : UnitAddCircle)‖ ≤
        (scalarBinomialCoefficientBudget D : ℝ)*C) ∧
    ∀ h ∈ U, (N : ℝ)*‖(((M : ℝ)*(P.eval 1+scalarPolynomialBinomialCoefficient Q D 2*(h : ℝ)+σ h) : ℝ) :
      UnitAddCircle)‖ ≤ C+(D+1 : ℕ)*C+(scalarBinomialCoefficientBudget D : ℝ)*B := by
  let C : ℝ := (S : ℝ)*A+(scalarTaylorTailBudget D : ℝ)*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hMono : ∀ i : ℕ, 2 ≤ i → i ≤ D →
      (N : ℝ)^i*‖(((M : ℝ)*P.coeff i : ℝ) : UnitAddCircle)‖ ≤ C := by
    obtain ⟨h,hh⟩ := hUne
    intro i hi hiD
    have he := scalar_difference_diagonal_coefficient_bound P Q D M i h N A B hQ hi hiD hN
      (hU h hh) hB (σ h) (hR h hh i (by omega) hiD) hHigherQ
    apply he.trans
    exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hMS) hA) le_rfl
  refine ⟨hMono,?_,?_⟩
  · intro i hi hiD
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact scalar_binomial_coefficient_mod_one P D M i 2 hiD hi (N : ℝ) C hNr hC hMono
  · intro h hh
    have he := scalar_difference_paper_linear_relation_bound P Q D M h N A B C hP hQ hD hZero
      hN (hU h hh) hB hC (σ h) (by simpa only [pow_one] using hR h hh 1 (by omega) (by omega)) hHigherQ hMono
    apply he.trans
    dsimp only [C]
    have hm := mul_le_mul_of_nonneg_right (by exact_mod_cast hMS : (M : ℝ) ≤ S) hA
    linarith

end Hindman168
