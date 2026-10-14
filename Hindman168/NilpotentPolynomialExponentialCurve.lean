import Hindman168.NoncommutativePolynomialCalculus

/-! The exact polynomial exponential curve t |-> exp(t*x) for nilpotent x.
Its coefficients and derivative are proved in any associative rational
algebra, and the right logarithmic derivative of an actual two-exponential
product is calculated using actual inverse exponentials. -/

noncomputable section
namespace Hindman168
open Polynomial Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

 omit [Algebra ℚ A] in
 theorem polynomial_linear_curve_nilpotent {x : A} (hx : IsNilpotent x) :
    IsNilpotent (monomial 1 x) := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m, ?_⟩
  rw [monomial_pow, hm, monomial_zero_right]

 theorem polynomial_exp_linear_coeff {x : A} (hx : IsNilpotent x) (k : ℕ) :
    (IsNilpotent.exp (monomial 1 x)).coeff k = (k.factorial : ℚ)⁻¹ • x ^ k := by
  obtain ⟨m, hm⟩ := hx
  have hp : (monomial 1 x) ^ m = 0 := by rw [monomial_pow, hm, monomial_zero_right]
  rw [IsNilpotent.exp_eq_sum hp]
  simp only [finsetSum_coeff, coeff_smul, monomial_pow, Nat.one_mul]
  rw [Finset.sum_eq_single k]
  · simp only [coeff_monomial, if_true]
  · intro j _ hj
    simp only [coeff_monomial, if_neg hj, smul_zero]
  · intro hk
    have hmle : m ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [pow_eq_zero_of_le hmle hm, coeff_monomial, ite_self, smul_zero]

 theorem polynomial_exp_linear_derivative {x : A} (hx : IsNilpotent x) :
    (IsNilpotent.exp (monomial 1 x)).derivative = C x * IsNilpotent.exp (monomial 1 x) := by
  apply Polynomial.ext
  intro k
  rw [coeff_derivative, polynomial_exp_linear_coeff hx, coeff_C_mul,
    polynomial_exp_linear_coeff hx, pow_succ']
  rw [smul_mul_assoc, mul_smul_comm]
  have hrat : ((k + 1).factorial : ℚ)⁻¹ * (↑(k + 1) : ℚ) = (k.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc]
    have hn : (↑(k + 1) : ℚ) ≠ 0 := by positivity
    rw [inv_mul_cancel₀ hn, mul_one]
  rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  rw [hrat]

 theorem polynomial_exp_product_right_log_derivative {x y : A}
    (hx : IsNilpotent x) (hy : IsNilpotent y) :
    (IsNilpotent.exp (monomial 1 x) * IsNilpotent.exp (monomial 1 y)).derivative *
      (IsNilpotent.exp (-(monomial 1 y)) * IsNilpotent.exp (-(monomial 1 x))) =
      C x + IsNilpotent.exp (monomial 1 x) * C y * IsNilpotent.exp (-(monomial 1 x)) := by
  have hpx := polynomial_linear_curve_nilpotent hx
  have hpy := polynomial_linear_curve_nilpotent hy
  rw [derivative_mul, polynomial_exp_linear_derivative hx, polynomial_exp_linear_derivative hy,
    add_mul]
  have h1 : (C x * IsNilpotent.exp (monomial 1 x) * IsNilpotent.exp (monomial 1 y)) *
      (IsNilpotent.exp (-(monomial 1 y)) * IsNilpotent.exp (-(monomial 1 x))) = C x := by
    simp only [mul_assoc]
    rw [← mul_assoc (IsNilpotent.exp (monomial 1 y)), IsNilpotent.exp_mul_exp_neg_self hpy,
      one_mul, IsNilpotent.exp_mul_exp_neg_self hpx, mul_one]
  have h2 : (IsNilpotent.exp (monomial 1 x) * (C y * IsNilpotent.exp (monomial 1 y))) *
      (IsNilpotent.exp (-(monomial 1 y)) * IsNilpotent.exp (-(monomial 1 x))) =
      IsNilpotent.exp (monomial 1 x) * C y * IsNilpotent.exp (-(monomial 1 x)) := by
    simp only [mul_assoc]
    rw [← mul_assoc (IsNilpotent.exp (monomial 1 y)), IsNilpotent.exp_mul_exp_neg_self hpy, one_mul]
  rw [h1, h2]

end Hindman168
