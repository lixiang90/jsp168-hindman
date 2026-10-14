import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Explicit integer polynomial size bounds at dyadic endpoints

The coefficient sum and total degree are computed from the actual finite
support. Every variable of the exposed tuple may have a different dyadic
interval, but its absolute value is bounded by twice the largest endpoint.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def integerPolynomialCoeffSize {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  ∑ d ∈ f.support, (f.coeff d).natAbs

noncomputable def integerPolynomialDyadicSize {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  integerPolynomialCoeffSize f * 2 ^ f.totalDegree

theorem integer_natAbs_finsetProd {ι : Type*} (S : Finset ι) (x : ι → ℤ) :
    (∏ i ∈ S, x i).natAbs = ∏ i ∈ S, (x i).natAbs := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.prod_insert hi, Int.natAbs_mul, ih]

theorem integerPolynomialCoeffSize_pos {σ : Type*} {f : MvPolynomial σ ℤ}
    (hf : f ≠ 0) : 0 < integerPolynomialCoeffSize f := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hf
  have hc : 0 < (f.coeff d).natAbs := Int.natAbs_pos.mpr (MvPolynomial.mem_support_iff.mp hd)
  exact hc.trans_le (Finset.single_le_sum (f := fun e => (f.coeff e).natAbs)
    (fun _ _ => Nat.zero_le _) hd)

theorem integerPolynomialDyadicSize_pos {σ : Type*} {f : MvPolynomial σ ℤ}
    (hf : f ≠ 0) : 0 < integerPolynomialDyadicSize f :=
  Nat.mul_pos (integerPolynomialCoeffSize_pos hf) (Nat.pow_pos (by decide))

theorem integerPolynomial_eval_natAbs_le {σ : Type*} (f : MvPolynomial σ ℤ)
    (x : σ → ℤ) {B : ℕ} (hB : 1 ≤ B) (hx : ∀ i, (x i).natAbs ≤ B) :
    (MvPolynomial.eval x f).natAbs ≤ integerPolynomialCoeffSize f * B ^ f.totalDegree := by
  rw [MvPolynomial.eval_eq]
  calc
    _ ≤ ∑ d ∈ f.support, (f.coeff d * ∏ i ∈ d.support, x i ^ d i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ d ∈ f.support, (f.coeff d).natAbs * B ^ f.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Int.natAbs_mul, integer_natAbs_finsetProd]
      simp only [Int.natAbs_pow]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ ∏ i ∈ d.support, B ^ d i :=
          Finset.prod_le_prod' (fun i _ => Nat.pow_le_pow_left (hx i) (d i))
        _ = B ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ B ^ f.totalDegree := Nat.pow_le_pow_right (by omega)
          (MvPolynomial.le_totalDegree hd)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem integerPolynomial_eval_dyadic_bound {σ : Type*} (f : MvPolynomial σ ℤ)
    (x : σ → ℤ) {A : ℕ} (hA : 1 ≤ A) (hx : ∀ i, (x i).natAbs ≤ 2 * A) :
    (MvPolynomial.eval x f).natAbs ≤ integerPolynomialDyadicSize f * A ^ f.totalDegree := by
  have h := integerPolynomial_eval_natAbs_le f x (B := 2 * A) (by omega) hx
  simpa only [integerPolynomialDyadicSize, mul_pow, mul_assoc] using h

end Hindman168
