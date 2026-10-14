import Hindman168.SmallPrimeResidueBound
import Hindman168.LargePrimeFactorCount

/-!
# Large-prime tests uniform at a common lower dyadic endpoint

A prime above sqrt L may still be below sqrt A for the other independent
tuple. Both branches are handled with their actual harmonic laws. The
bound retains the exception where the prime divides the main leading
coefficient. These exceptions are left for variable induction.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem primePolynomial_common_large_prime_bound {L q A : ℕ} [Fact q.Prime]
    (hL : Real.exp 2 ≤ (L : ℝ)) (hLA : L ≤ A) (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hsmall : (q : ℝ) ≤ Real.sqrt A →
      ∀ a < q, primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ))
    (hlarge : Real.sqrt (L : ℝ) < q) (f : Polynomial ℤ)
    (hcoeff : ¬ (q : ℤ) ∣ f.leadingCoeff) :
    event (primePoolMass A (2 * A)) (fun n => (q : ℤ) ∣ f.eval (n : ℤ)) ≤
      (f.natDegree : ℝ) * (1032 * Real.log (L : ℝ) / Real.sqrt L) := by
  have hLpos : (0 : ℝ) < L := (Real.exp_pos 2).trans_le hL
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLpos
  have hlog : 1 ≤ Real.log (L : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hL
    rw [Real.log_exp] at h
    linarith
  by_cases hs : (q : ℝ) ≤ Real.sqrt A
  · have he := smallPrime_polynomial_fiber_bound (hsmall hs) f hcoeff
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      1032 / (q : ℝ) ≤ 1032 / Real.sqrt L :=
        div_le_div_of_nonneg_left (by norm_num) hsqrt hlarge.le
      _ ≤ 1032 * Real.log (L : ℝ) / Real.sqrt L :=
        div_le_div_of_nonneg_right (by nlinarith) hsqrt.le
  · have he := primePolynomial_large_prime_divisibility_uniform hL hLA hA hH
      (le_of_not_ge hs) f hcoeff
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact div_le_div_of_nonneg_right (by nlinarith) hsqrt.le

noncomputable def integerPolynomialMainLeading {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin n) ℤ := (MvPolynomial.finSuccEquiv ℤ n f).leadingCoeff

noncomputable def integerPolynomialMainFiber {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (x : Fin n → ℕ) : Polynomial ℤ :=
  (MvPolynomial.finSuccEquiv ℤ n f).map (MvPolynomial.eval (fun i => (x i : ℤ)))

theorem integerPolynomialMainFiber_eval {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (x : Fin n → ℕ) (a : ℕ) :
    (integerPolynomialMainFiber f x).eval (a : ℤ) =
      MvPolynomial.eval (fun i => ((Fin.cons a x : Fin (n + 1) → ℕ) i : ℤ)) f := by
  have hc : (fun i => ((Fin.cons a x : Fin (n + 1) → ℕ) i : ℤ)) =
      Fin.cons (a : ℤ) (fun i => (x i : ℤ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
  rfl

theorem integerPolynomialMainFiber_natDegree_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (x : Fin n → ℕ) :
    (integerPolynomialMainFiber f x).natDegree ≤ f.degreeOf 0 :=
  Polynomial.natDegree_map_le.trans_eq (MvPolynomial.natDegree_finSuccEquiv f)

theorem integerPolynomialMainLeading_ne_zero {n : ℕ}
    {f : MvPolynomial (Fin (n + 1)) ℤ} (hf : f ≠ 0) :
    integerPolynomialMainLeading f ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (EmbeddingLike.map_ne_zero_iff.mpr hf)

theorem integerPolynomialMainFiber_leadingCoeff {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (x : Fin n → ℕ)
    (hx : MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) ≠ 0) :
    (integerPolynomialMainFiber f x).leadingCoeff =
      MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) :=
  Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hx

theorem primePolynomialMainFiber_large_bound {n L q A : ℕ} [Fact q.Prime]
    (hL : Real.exp 2 ≤ (L : ℝ)) (hLA : L ≤ A) (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hsmall : (q : ℝ) ≤ Real.sqrt A →
      ∀ a < q, primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ))
    (hlarge : Real.sqrt (L : ℝ) < q)
    (f : MvPolynomial (Fin (n + 1)) ℤ) (x : Fin n → ℕ) :
    event (primePoolMass A (2 * A)) (fun a =>
      ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => ((Fin.cons a x : Fin (n + 1) → ℕ) i : ℤ)) f) ≤
        (f.degreeOf 0 : ℝ) * (1032 * Real.log (L : ℝ) / Real.sqrt L) := by
  have hlog : 0 ≤ Real.log (L : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 2) hL
    rw [Real.log_exp] at h
    linarith
  have hb : 0 ≤ 1032 * Real.log (L : ℝ) / Real.sqrt L := by positivity
  by_cases hx : (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f)
  · simp only [hx, not_true_eq_false, false_and, event_false]
    positivity
  · have hx0 : MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) ≠ 0 :=
      fun h => hx (h.symm ▸ dvd_zero _)
    have hc : ¬ (q : ℤ) ∣ (integerPolynomialMainFiber f x).leadingCoeff := by
      rw [integerPolynomialMainFiber_leadingCoeff f x hx0]
      exact hx
    have he := primePolynomial_common_large_prime_bound hL hLA hA hH hsmall hlarge
      (integerPolynomialMainFiber f x) hc
    simp only [hx, not_false_eq_true, true_and, ← integerPolynomialMainFiber_eval] at ⊢
    exact he.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast integerPolynomialMainFiber_natDegree_le f x) hb)

theorem primePolynomialMainFiber_small_bound {n q A : ℕ} [Fact q.Prime]
    (hcap : ∀ a < q, primePoolResidueMass q A (2 * A) a ≤ 1032 / (q : ℝ))
    (f : MvPolynomial (Fin (n + 1)) ℤ) (x : Fin n → ℕ) :
    event (primePoolMass A (2 * A)) (fun a =>
      ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => ((Fin.cons a x : Fin (n + 1) → ℕ) i : ℤ)) f) ≤
        (f.degreeOf 0 : ℝ) * (1032 / (q : ℝ)) := by
  have hb : 0 ≤ 1032 / (q : ℝ) := by positivity
  by_cases hx : (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f)
  · simp only [hx, not_true_eq_false, false_and, event_false]
    positivity
  · have hx0 : MvPolynomial.eval (fun i => (x i : ℤ)) (integerPolynomialMainLeading f) ≠ 0 :=
      fun h => hx (h.symm ▸ dvd_zero _)
    have hc : ¬ (q : ℤ) ∣ (integerPolynomialMainFiber f x).leadingCoeff := by
      rw [integerPolynomialMainFiber_leadingCoeff f x hx0]
      exact hx
    have he := smallPrime_polynomial_fiber_bound hcap (integerPolynomialMainFiber f x) hc
    simp only [hx, not_false_eq_true, true_and, ← integerPolynomialMainFiber_eval] at ⊢
    exact he.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast integerPolynomialMainFiber_natDegree_le f x) hb)

end Hindman168
