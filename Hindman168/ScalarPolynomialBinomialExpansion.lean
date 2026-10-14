import Hindman168.ScalarPolynomialStirlingExpansion

namespace Hindman168
open Polynomial
open scoped BigOperators

noncomputable def scalarBinomialPolynomial (i : ℕ) : ℝ[X] :=
  C ((i.factorial : ℝ)⁻¹)*descPochhammer ℝ i

noncomputable def scalarPolynomialBinomialCoefficient (p : ℝ[X]) (D i : ℕ) : ℝ :=
  (i.factorial : ℝ)*∑ j ∈ Finset.range (D+1), p.coeff j*(Nat.stirlingSecond j i : ℝ)

theorem scalar_polynomial_stirling_expansion_bounded (n D : ℕ) (hn : n ≤ D) :
    (X : ℝ[X])^n = ∑ i ∈ Finset.range (D+1),
      C (Nat.stirlingSecond n i : ℝ)*descPochhammer ℝ i := by
  rw [scalar_polynomial_stirling_expansion]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro i _ hi
  have hni : n < i := by
    have := Finset.mem_range.not.mp hi
    omega
  simp [Nat.stirlingSecond_eq_zero_of_lt hni]

theorem scalar_binomial_polynomial_eval_nat (i n : ℕ) :
    (scalarBinomialPolynomial i).eval (n : ℝ) = (n.choose i : ℝ) := by
  rw [scalarBinomialPolynomial, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div,
    div_eq_mul_inv]
  exact mul_comm _ _

/-- Actual binomial expansion of the original polynomial. Its coefficients
are integer triangular combinations of the original monomial coefficients. -/
theorem scalar_polynomial_binomial_expansion (p : ℝ[X]) (D : ℕ)
    (hp : p.natDegree ≤ D) :
    p = ∑ i ∈ Finset.range (D+1),
      C (scalarPolynomialBinomialCoefficient p D i)*scalarBinomialPolynomial i := by
  have hterm (i : ℕ) :
      C (scalarPolynomialBinomialCoefficient p D i)*scalarBinomialPolynomial i =
        C (∑ j ∈ Finset.range (D+1), p.coeff j*(Nat.stirlingSecond j i : ℝ))*
          descPochhammer ℝ i := by
    dsimp only [scalarPolynomialBinomialCoefficient, scalarBinomialPolynomial]
    rw [map_mul]
    calc
      _ = (C (i.factorial : ℝ)*C ((i.factorial : ℝ)⁻¹))*
          (C (∑ j ∈ Finset.range (D+1), p.coeff j*(Nat.stirlingSecond j i : ℝ))*
            descPochhammer ℝ i) := by ring
      _ = _ := by rw [← map_mul, mul_inv_cancel₀ (by positivity : (i.factorial : ℝ) ≠ 0), C_1, one_mul]
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < D+1)]
  conv_rhs => simp only [hterm, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [scalar_polynomial_stirling_expansion_bounded j D
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Hindman168
