import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Factorial.Basic

/-! An actual finite operator polynomial antiderivative for the truncated
adjoint series. It is differentiated directly, without an assumed
exponential differential or logarithmic derivative formula. -/

namespace Hindman168
open Finset
open scoped ContDiff

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

noncomputable def adjointPrimitivePolynomial (B : A) (k : ℕ) (t : ℝ) : A :=
  ∑ j ∈ range k, (((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) * t ^ (j + 1)) • B ^ j

 theorem adjointPrimitivePolynomial_zero (B : A) (k : ℕ) :
    adjointPrimitivePolynomial B k 0 = 0 := by
  simp only [adjointPrimitivePolynomial, zero_pow (Nat.succ_ne_zero _), mul_zero,
    zero_smul, sum_const_zero]

 theorem adjointPrimitivePolynomial_coefficient (j : ℕ) (t : ℝ) :
    ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) * ((j + 1 : ℝ) * t ^ j) =
      (j.factorial : ℝ)⁻¹ * (-t) ^ j := by
  rw [neg_eq_neg_one_mul, mul_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hs : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  rw [one_pow, mul_one, ← mul_pow]
  congr 1
  ring

 theorem adjointPrimitivePolynomial_hasDerivAt (B : A) (k : ℕ) (t : ℝ) :
    HasDerivAt (adjointPrimitivePolynomial B k)
      (∑ j ∈ range k, (j.factorial : ℝ)⁻¹ • ((-t) • B) ^ j) t := by
  have h : ∀ j ∈ range k,
      HasDerivAt
        (fun s : ℝ => (((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) * s ^ (j + 1)) • B ^ j)
        ((j.factorial : ℝ)⁻¹ • ((-t) • B) ^ j) t := by
    intro j _
    have hd := (((hasDerivAt_id t).pow (j + 1)).const_mul
      ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ))).smul_const (B ^ j)
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one] at hd
    rw [adjointPrimitivePolynomial_coefficient] at hd
    simp only [smul_pow, smul_smul]
    convert! hd using 1
  convert! HasDerivAt.sum h using 1
  funext s
  simp only [adjointPrimitivePolynomial, Finset.sum_apply]

 theorem eq_adjointPrimitivePolynomial_of_hasDerivAt
    {K : ℝ → A} (B : A) (k : ℕ) (h0 : K 0 = 0)
    (hK : ∀ t : ℝ, HasDerivAt K
      (∑ j ∈ range k, (j.factorial : ℝ)⁻¹ • ((-t) • B) ^ j) t) (t : ℝ) :
    K t = adjointPrimitivePolynomial B k t := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u => K u - adjointPrimitivePolynomial B k u) 0 s := by
    intro s
    have h := (hK s).sub (adjointPrimitivePolynomial_hasDerivAt B k s)
    simp only [sub_self] at h
    convert! h using 1
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [h0, adjointPrimitivePolynomial_zero, sub_self] at he
  exact sub_eq_zero.mp he

end Hindman168
