import Hindman168.IntegerPolynomialValueBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Boundedly many large prime factors of an actual nonzero polynomial value

Distinct prime factors have a product dividing the value. Squaring this
product avoids logarithms and square roots in the counting argument. If
n <= C A^d and A >= C^2, there are at most 2d+1 distinct prime factors
above sqrt A, independent of A and of the dyadic endpoint ratios.
-/

namespace Hindman168

open scoped BigOperators Classical

def largePrimeDivisors (A n : ℕ) : Finset ℕ := n.primeFactors.filter (fun q => A < q ^ 2)

theorem mem_largePrimeDivisors {A n q : ℕ} (hn : n ≠ 0) :
    q ∈ largePrimeDivisors A n ↔ q.Prime ∧ q ∣ n ∧ A < q ^ 2 := by
  simp only [largePrimeDivisors, Finset.mem_filter, Nat.mem_primeFactors]
  tauto

theorem largePrimeDivisors_product_dvd (A n : ℕ) :
    (∏ q ∈ largePrimeDivisors A n, q) ∣ n :=
  (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd n)

theorem endpoint_pow_largePrimeDivisors_card_le_square {A n : ℕ} (hn : n ≠ 0) :
    A ^ (largePrimeDivisors A n).card ≤ n ^ 2 := by
  have hprod : (∏ q ∈ largePrimeDivisors A n, q) ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (largePrimeDivisors_product_dvd A n)
  calc
    _ = ∏ _q ∈ largePrimeDivisors A n, A := by simp
    _ ≤ ∏ q ∈ largePrimeDivisors A n, q ^ 2 :=
      Finset.prod_le_prod' (fun q hq => (Finset.mem_filter.mp hq).2.le)
    _ = (∏ q ∈ largePrimeDivisors A n, q) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hprod 2

theorem largePrimeDivisors_card_le {A n C d : ℕ} (hA : 2 ≤ A)
    (hn : n ≠ 0) (hnsize : n ≤ C * A ^ d) (hC : C ^ 2 ≤ A) :
    (largePrimeDivisors A n).card ≤ 2 * d + 1 := by
  apply (Nat.pow_le_pow_iff_right (by omega : 1 < A)).mp
  calc
    _ ≤ n ^ 2 := endpoint_pow_largePrimeDivisors_card_le_square hn
    _ ≤ (C * A ^ d) ^ 2 := Nat.pow_le_pow_left hnsize 2
    _ = C ^ 2 * A ^ (2 * d) := by rw [mul_pow, ← pow_mul, Nat.mul_comm d 2]
    _ ≤ A * A ^ (2 * d) := Nat.mul_le_mul_right _ hC
    _ = A ^ (2 * d + 1) := by rw [pow_succ, Nat.mul_comm]

theorem sqrt_lt_prime_iff_square_lt {A q : ℕ} :
    Real.sqrt (A : ℝ) < (q : ℝ) ↔ A < q ^ 2 := by
  rw [Real.sqrt_lt (Nat.cast_nonneg A) (Nat.cast_nonneg q)]
  norm_cast

theorem integerPolynomial_largePrimeDivisors_card_le {σ : Type*}
    (f : MvPolynomial σ ℤ) (x : σ → ℤ) {A : ℕ} (hA : 2 ≤ A)
    (hx : ∀ i, (x i).natAbs ≤ 2 * A) (hvalue : MvPolynomial.eval x f ≠ 0)
    (hsize : (integerPolynomialDyadicSize f) ^ 2 ≤ A) :
    (largePrimeDivisors A (MvPolynomial.eval x f).natAbs).card ≤ 2 * f.totalDegree + 1 := by
  exact largePrimeDivisors_card_le hA (Int.natAbs_ne_zero.mpr hvalue)
    (integerPolynomial_eval_dyadic_bound f x (by omega) hx) hsize

end Hindman168
