import Hindman168.NilpotentPolynomialExponentialCurve

/-! A finite dexp identity derived from the already proved Hadamard formula.
Formal differentiation is the actual rational-linear endomorphism on
noncommutative coefficient polynomials. Its commutator with left
multiplication is minus multiplication by the derivative. -/

noncomputable section
namespace Hindman168
open Polynomial Module Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

 def polynomialDerivativeQ : End ℚ (Polynomial A) := Polynomial.derivative.restrictScalars ℚ

 theorem polynomialDerivativeQ_apply (p : Polynomial A) : polynomialDerivativeQ p = p.derivative := rfl

 theorem polynomial_left_commutator (p q : Polynomial A) :
    commutatorEndQ (LinearMap.mulLeft ℚ p) (LinearMap.mulLeft ℚ q) =
      LinearMap.mulLeft ℚ (commutatorEndQ p q) := by
  apply LinearMap.ext
  intro r
  change p * (q * r) - q * (p * r) = (p * q - q * p) * r
  rw [sub_mul]
  simp only [mul_assoc]

 theorem polynomial_derivative_commutator (p : Polynomial A) :
    commutatorEndQ (LinearMap.mulLeft ℚ p) polynomialDerivativeQ =
      -(LinearMap.mulLeft ℚ p.derivative) := by
  apply LinearMap.ext
  intro q
  change p * q.derivative - (p * q).derivative = -(p.derivative * q)
  rw [derivative_mul]
  abel

 theorem polynomial_derivative_commutator_pow (p : Polynomial A) (m : ℕ) :
    (commutatorEndQ (LinearMap.mulLeft ℚ p) ^ (m + 1)) polynomialDerivativeQ =
      -(LinearMap.mulLeft ℚ ((commutatorEndQ p ^ m) p.derivative)) := by
  induction m with
  | zero =>
    simpa only [Nat.zero_add, pow_one, pow_zero, Module.End.one_apply] using
      polynomial_derivative_commutator p
  | succ m ih =>
    rw [pow_succ']
    change commutatorEndQ (LinearMap.mulLeft ℚ p)
      ((commutatorEndQ (LinearMap.mulLeft ℚ p) ^ (m + 1)) polynomialDerivativeQ) = _
    rw [ih, map_neg, polynomial_left_commutator, pow_succ']
    rfl

 theorem polynomial_nilpotent_exp_dexp {p : Polynomial A} (hp : IsNilpotent p) :
    ∃ m : ℕ, 0 < m ∧ (IsNilpotent.exp p).derivative * IsNilpotent.exp (-p) =
      ∑ k ∈ range m, ((k + 1).factorial : ℚ)⁻¹ • ((commutatorEndQ p ^ k) p.derivative) := by
  have hL := nilpotent_mulLeftQ hp
  obtain ⟨m, hm⟩ := commutatorEndQ_nilpotent hL
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have hs : (IsNilpotent.exp (commutatorEndQ (LinearMap.mulLeft ℚ p)) polynomialDerivativeQ)
      (1 : Polynomial A) =
      -(∑ k ∈ range (m + 1), ((k + 1).factorial : ℚ)⁻¹ • ((commutatorEndQ p ^ k) p.derivative)) := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (by omega : m ≤ (m + 1) + 1) hm)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Module.End.one_apply, polynomialDerivativeQ_apply, derivative_one,
      smul_zero, add_zero]
    simp only [polynomial_derivative_commutator_pow, LinearMap.neg_apply,
      LinearMap.mulLeft_apply, mul_one, smul_neg, Finset.sum_neg_distrib]
  have hr : (IsNilpotent.exp (commutatorEndQ (LinearMap.mulLeft ℚ p)) polynomialDerivativeQ)
      (1 : Polynomial A) = IsNilpotent.exp p * (IsNilpotent.exp (-p)).derivative := by
    rw [exp_commutatorEndQ_apply hL]
    change IsNilpotent.exp (LinearMap.mulLeft ℚ p)
      (polynomialDerivativeQ (IsNilpotent.exp (-(LinearMap.mulLeft ℚ p)) (1 : Polynomial A))) = _
    have hn : -(LinearMap.mulLeft ℚ p) = LinearMap.mulLeft ℚ (-p) := by
      apply LinearMap.ext
      intro q
      change -(p * q) = (-p) * q
      rw [neg_mul]
    rw [hn, exp_mulLeftQ_apply hp.neg, mul_one, polynomialDerivativeQ_apply, exp_mulLeftQ_apply hp]
  have he : (IsNilpotent.exp p).derivative * IsNilpotent.exp (-p) +
      IsNilpotent.exp p * (IsNilpotent.exp (-p)).derivative = 0 := by
    rw [← derivative_mul, IsNilpotent.exp_mul_exp_neg_self hp, derivative_one]
  rw [← hr, hs] at he
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)

end Hindman168
