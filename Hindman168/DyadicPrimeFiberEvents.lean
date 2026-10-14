import Hindman168.UniformLargePrimeFibers
import Hindman168.IndependentFiberEvents

/-!
# Independent dyadic polynomial divisibility events outside main exceptions

The main variable is coordinate zero. Its remaining coordinates retain
their individual prime laws. Averaging the proved fiber bound gives the
same bound for the entire tuple without any endpoint-ratio factor.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem unequalDyadicPrime_main_small_divisibility_bound {n q : ℕ} [Fact q.Prime]
    (e : Fin (n + 1) → ℕ)
    (hH : ∀ i, 0 < primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1)))
    (hcap : ∀ a < q, primePoolResidueMass q (2 ^ e 0) (2 ^ (e 0 + 1)) a ≤ 1032 / (q : ℝ))
    (f : MvPolynomial (Fin (n + 1)) ℤ) :
    event (unequalDyadicPrimeMass e) (fun x =>
      ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail x i : ℤ)) (integerPolynomialMainLeading f) ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) f) ≤
        (f.degreeOf 0 : ℝ) * (1032 / (q : ℝ)) := by
  apply event_piMass_main_fiber_le _ _ (fun _ => primePoolMass_nonneg _ _)
    (fun i => primePoolMass_total (hH i))
  intro x
  have h := primePolynomialMainFiber_small_bound (q := q) (A := 2 ^ e 0)
    (by simpa only [Nat.pow_succ, Nat.mul_comm] using hcap) f x
  simpa only [Fin.tail_cons, Nat.pow_succ, Nat.mul_comm] using h

theorem unequalDyadicPrime_main_large_divisibility_bound {n L q : ℕ} [Fact q.Prime]
    (e : Fin (n + 1) → ℕ)
    (hH : ∀ i, 0 < primePoolHarmonicMass (2 ^ e i) (2 ^ (e i + 1)))
    (hL : Real.exp 2 ≤ (L : ℝ)) (hLA : L ≤ 2 ^ e 0) (hA : 2 ≤ 2 ^ e 0)
    (hPNT : 1 / (8 * Real.log (2 ^ e 0 : ℕ)) ≤
      primePoolHarmonicMass (2 ^ e 0) (2 ^ (e 0 + 1)))
    (hsmall : (q : ℝ) ≤ Real.sqrt (2 ^ e 0 : ℕ) →
      ∀ a < q, primePoolResidueMass q (2 ^ e 0) (2 ^ (e 0 + 1)) a ≤ 1032 / (q : ℝ))
    (hlarge : Real.sqrt (L : ℝ) < q) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    event (unequalDyadicPrimeMass e) (fun x =>
      ¬ (q : ℤ) ∣ MvPolynomial.eval (fun i => (Fin.tail x i : ℤ)) (integerPolynomialMainLeading f) ∧
      (q : ℤ) ∣ MvPolynomial.eval (fun i => (x i : ℤ)) f) ≤
        (f.degreeOf 0 : ℝ) * (1032 * Real.log (L : ℝ) / Real.sqrt L) := by
  apply event_piMass_main_fiber_le _ _ (fun _ => primePoolMass_nonneg _ _)
    (fun i => primePoolMass_total (hH i))
  intro x
  have h := primePolynomialMainFiber_large_bound hL hLA hA (q := q)
    (by simpa only [Nat.pow_succ, Nat.mul_comm] using hPNT)
    (by simpa only [Nat.pow_succ, Nat.mul_comm] using hsmall) hlarge f x
  simpa only [Fin.tail_cons, Nat.pow_succ, Nat.mul_comm] using h

end Hindman168
