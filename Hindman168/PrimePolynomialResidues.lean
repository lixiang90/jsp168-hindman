import Hindman168.PrimeResidueAtomBounds
import Hindman168.UnitResidueRepresentatives

/-!
# Prime-divisor tests for one polynomial fiber

The actual prime law is pushed to ZMod, retaining its harmonic weights.
Root counts require the reduced polynomial to be nonzero. A nondivisible
leading coefficient supplies this condition, leaving the exceptional
leading-coefficient divisibility event explicit for the later induction.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def primePoolModMass (q A B : ℕ) : Mass (ZMod q) :=
  (primePoolMass A B).mapDomain (fun n : ℕ => (n : ZMod q))

theorem primePoolModMass_apply_event (q A B : ℕ) [NeZero q] (r : ZMod q) :
    primePoolModMass q A B r = event (primePoolMass A B) (fun n => n % q = r.val) := by
  rw [primePoolModMass, push_apply, event_eq_sum _ _ (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro n _
  have he : r = (n : ZMod q) ↔ n % q = r.val := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast] using hv.symm
    · intro h
      apply ZMod.val_injective q
      simpa only [ZMod.val_natCast] using h.symm
  simp only [he]
  by_cases hn : n % q = r.val <;> simp only [hn, if_true, if_false]

theorem integerPolynomial_univariate_natCast_eval (q n : ℕ) (f : Polynomial ℤ) :
    (f.map (Int.castRingHom (ZMod q))).eval (n : ZMod q) =
      ((f.eval (n : ℤ) : ℤ) : ZMod q) := by
  rw [Polynomial.eval_map]
  simp

theorem integerPolynomial_mod_ne_zero_of_leadingCoeff {q : ℕ}
    (f : Polynomial ℤ) (hcoeff : ¬ (q : ℤ) ∣ f.leadingCoeff) :
    f.map (Int.castRingHom (ZMod q)) ≠ 0 := by
  intro hzero
  have hc := congrArg (fun p : Polynomial (ZMod q) => p.coeff f.natDegree) hzero
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
  exact hcoeff ((CharP.intCast_eq_zero_iff (ZMod q) q _).mp hc)

theorem primePolynomial_divisibility_atom_bound {q A B : ℕ} [Fact q.Prime]
    (f : Polynomial ℤ) (hf : f.map (Int.castRingHom (ZMod q)) ≠ 0)
    {b : ℝ} (hb : 0 ≤ b) (hcap : ∀ r, primePoolModMass q A B r ≤ b) :
    event (primePoolMass A B) (fun n => (q : ℤ) ∣ f.eval (n : ℤ)) ≤
      (f.natDegree : ℝ) * b := by
  have he := polynomial_zero_event_le (f.map (Int.castRingHom (ZMod q))) hf
    (primePoolModMass q A B) hb hcap
  rw [primePoolModMass, event_map] at he
  simp_rw [integerPolynomial_univariate_natCast_eval, CharP.intCast_eq_zero_iff] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Polynomial.natDegree_map_le (f := Int.castRingHom (ZMod q)) (p := f)) hb)

theorem primePolynomial_large_prime_divisibility_bound {q A : ℕ} [Fact q.Prime]
    (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hlarge : Real.sqrt (A : ℝ) ≤ q) (f : Polynomial ℤ)
    (hcoeff : ¬ (q : ℤ) ∣ f.leadingCoeff) :
    event (primePoolMass A (2 * A)) (fun n => (q : ℤ) ∣ f.eval (n : ℤ)) ≤
      (f.natDegree : ℝ) * (16 * Real.log (A : ℝ) / Real.sqrt A) := by
  have hlog : 0 ≤ Real.log (A : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < A))).le
  apply primePolynomial_divisibility_atom_bound f
    (integerPolynomial_mod_ne_zero_of_leadingCoeff f hcoeff) (by positivity)
  intro r
  rw [primePoolModMass_apply_event, ← primePoolResidueMass_eq_event]
  exact dyadicPrimeResidueMass_large_modulus_bound hA hH
    (Fact.out (p := q.Prime)).pos (ZMod.val_lt r) hlarge

theorem primePolynomial_large_prime_divisibility_uniform {L q A : ℕ} [Fact q.Prime]
    (hL : Real.exp 2 ≤ (L : ℝ)) (hLA : L ≤ A) (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hlarge : Real.sqrt (A : ℝ) ≤ q) (f : Polynomial ℤ)
    (hcoeff : ¬ (q : ℤ) ∣ f.leadingCoeff) :
    event (primePoolMass A (2 * A)) (fun n => (q : ℤ) ∣ f.eval (n : ℤ)) ≤
      (f.natDegree : ℝ) * (16 * Real.log (L : ℝ) / Real.sqrt L) := by
  have hLAr : (L : ℝ) ≤ A := by exact_mod_cast hLA
  have hm := Real.log_div_sqrt_antitoneOn hL (hL.trans hLAr) hLAr
  calc
    _ ≤ (f.natDegree : ℝ) * (16 * Real.log (A : ℝ) / Real.sqrt A) :=
      primePolynomial_large_prime_divisibility_bound hA hH hlarge f hcoeff
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 16))
      (Nat.cast_nonneg _)

end Hindman168
