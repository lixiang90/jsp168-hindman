import Hindman168.PolynomialLieCoefficients

/-! Finite polynomial calculus with genuinely noncommuting coefficients.
The derivative of a power retains every possible insertion of the derivative;
no commutative power rule is applied to matrix-valued polynomials. -/

noncomputable section
namespace Hindman168
open Polynomial Finset

variable {A : Type*} [Ring A]

 theorem polynomial_derivative_pow_noncomm (p : Polynomial A) (m : ℕ) :
    (p ^ m).derivative =
      ∑ i ∈ range m, p ^ i * p.derivative * p ^ (m - 1 - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, derivative_mul, ih, sum_mul, sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have he : m - 1 - i + 1 = m + 1 - 1 - i := by
        have hl := Finset.mem_range.mp hi
        omega
      rw [mul_assoc, ← pow_succ, he]
    · simp

variable [Algebra ℚ A]

 theorem polynomial_coeff_from_derivative (p : Polynomial A) (n : ℕ) :
    p.coeff (n + 1) = ((n + 1 : ℚ)⁻¹) • p.derivative.coeff n := by
  simp only [coeff_derivative, ← Nat.cast_add_one]
  rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  have hn : (↑(n + 1) : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ hn, one_smul]

 theorem polynomial_nilpotent_exp_derivative {p : Polynomial A} {m : ℕ} (hp : p ^ m = 0) :
    (IsNilpotent.exp p).derivative =
      ∑ k ∈ range m, (k.factorial : ℚ)⁻¹ •
        (∑ i ∈ range k, p ^ i * p.derivative * p ^ (k - 1 - i)) := by
  rw [IsNilpotent.exp_eq_sum hp, derivative_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_smul, polynomial_derivative_pow_noncomm]

variable {R : Type*} [CommRing R] [Algebra R A] [Algebra ℚ R]
local instance calculusAmbientLieRing : LieRing A := LieRing.ofAssociativeRing
local instance calculusPolynomialLieRing : LieRing (Polynomial A) := LieRing.ofAssociativeRing

 theorem polynomialLieSubalgebra_of_derivative (V : LieSubalgebra R A)
    {p : Polynomial A} (h0 : p.coeff 0 ∈ V)
    (hd : p.derivative ∈ polynomialLieSubalgebra V) : p ∈ polynomialLieSubalgebra V := by
  intro n
  cases n with
  | zero => exact h0
  | succ n =>
    rw [polynomial_coeff_from_derivative]
    exact (V.toSubmodule.restrictScalars ℚ).smul_mem _ (hd n)

 theorem polynomialLieSubalgebra_derivative_iff (V : LieSubalgebra R A) (p : Polynomial A) :
    p ∈ polynomialLieSubalgebra V ↔ p.coeff 0 ∈ V ∧ p.derivative ∈ polynomialLieSubalgebra V :=
  ⟨fun h => ⟨h 0, polynomialLieSubalgebra_derivative_mem V h⟩,
    fun h => polynomialLieSubalgebra_of_derivative V h.1 h.2⟩

end Hindman168
