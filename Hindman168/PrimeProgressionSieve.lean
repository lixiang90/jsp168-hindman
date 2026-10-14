import Hindman168.ArithmeticIntervalSieve

/-!
# Actual prime progression counts and harmonic probabilities from the sieve

Primes above the cutoff z are coprime to the actual sieving product.
Their count in a prescribed residue class is therefore bounded by the
sifted sum of the arithmetic interval. The final probability estimate
uses the original 1/p law and its proved harmonic lower bound.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def primeProgressionWindow (q a A T : ℕ) : Finset ℕ :=
  (Finset.Ico A (A + T)).filter (fun n => n.Prime ∧ n % q = a)

theorem prime_above_cutoff_coprime_sieveProduct {q z n : ℕ} (hn : n.Prime)
    (hzn : z < n) : (sievePrimeProduct q z).Coprime n := by
  apply Nat.Coprime.symm
  apply hn.coprime_iff_not_dvd.mpr
  intro hd
  have hp := hd.trans (sievePrimeProduct_dvd_primorial q z)
  exact hzn.not_ge (hn.dvd_primorial_iff.mp hp)

theorem primeProgressionWindow_card_le_sifted {q z A T a : ℕ} (hzA : z < A) :
    ((primeProgressionWindow q a A T).card : ℝ) ≤
      (arithmeticIntervalSieve q z A T a).siftedSum := by
  change ((primeProgressionWindow q a A T).card : ℝ) ≤
    ∑ n ∈ Finset.Ico A (A + T), if (sievePrimeProduct q z).Coprime n then
      (if n % q = a then 1 else 0) else 0
  rw [primeProgressionWindow, Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro n hn
  by_cases he : n.Prime ∧ n % q = a
  · have hc := prime_above_cutoff_coprime_sieveProduct (q := q) he.1
      (hzA.trans_le (Finset.mem_Ico.mp hn).1)
    simp only [if_pos he, if_pos hc, if_pos he.2, le_refl]
  · rw [if_neg he]
    split_ifs <;> norm_num

theorem primeProgressionWindow_card_upper {q : ℕ} (hq : q.Prime)
    {z A T a : ℕ} (hz : 1 ≤ z) (hzA : z < A) (ha : a < q) :
    ((primeProgressionWindow q a A T).card : ℝ) ≤
      4 * ((T : ℝ) / q) / Real.log (z + 1 : ℕ) + (z : ℝ) ^ 4 :=
  (primeProgressionWindow_card_le_sifted hzA).trans (arithmeticIntervalSieve_upper hq hz A T ha)

theorem primePool_residue_event_count_bound {A T q a : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A (A + T)) :
    event (primePoolMass A (A + T)) (fun n => n % q = a) ≤
      ((primeProgressionWindow q a A T).card : ℝ) /
        ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by
  have he : event (primePoolMass A (A + T)) (fun n => n % q = a) =
      ∑ n ∈ primeProgressionWindow q a A T, primePoolMass A (A + T) n := by
    rw [event_eq_sum _ _ (primePoolMass_support A (A + T))]
    simp only [primeProgressionWindow, primePool, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime <;> by_cases hr : n % q = a <;>
      simp only [hp, hr, if_true, if_false, true_and, false_and]
  have hb : 0 ≤ 1 / ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by positivity
  rw [he]
  calc
    (∑ n ∈ primeProgressionWindow q a A T,
      primePoolMass A (A + T) n) ≤
      ∑ _n ∈ primeProgressionWindow q a A T,
        1 / ((A : ℝ) * primePoolHarmonicMass A (A + T)) :=
      Finset.sum_le_sum (fun n _ => primePool_max_atom hA hH n)
    _ = ((primeProgressionWindow q a A T).card : ℝ) *
        (1 / ((A : ℝ) * primePoolHarmonicMass A (A + T))) := by simp
    _ = ((primeProgressionWindow q a A T).card : ℝ) /
        ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by ring

theorem dyadicPrime_residue_sieve_probability {q A z a : ℕ} (hq : q.Prime)
    (hA : 2 ≤ A) (hz : 1 ≤ z) (hzA : z < A) (ha : a < q)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A)) :
    primePoolResidueMass q A (2 * A) a ≤
      8 * (Real.log (A : ℝ) / A) *
        (4 * ((A : ℝ) / q) / Real.log (z + 1 : ℕ) + (z : ℝ) ^ 4) := by
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hHpos : 0 < primePoolHarmonicMass A (2 * A) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hlog)).trans_le hH
  have ht : A + A = 2 * A := by omega
  have hc := primeProgressionWindow_card_upper hq (T := A) hz hzA ha
  have hp := primePool_residue_event_count_bound (T := A) (q := q) (a := a)
    (by omega : 0 < A) (by simpa only [ht] using hHpos)
  have hrec : 1 / primePoolHarmonicMass A (2 * A) ≤ 8 * Real.log (A : ℝ) := by
    apply (div_le_iff₀ hHpos).mpr
    have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hlog)).mp hH
    simpa only [mul_comm] using hh
  rw [ht] at hp
  rw [primePoolResidueMass_eq_event]
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  calc
    _ ≤ ((primeProgressionWindow q a A A).card : ℝ) /
        ((A : ℝ) * primePoolHarmonicMass A (2 * A)) := hp
    _ = ((primeProgressionWindow q a A A).card : ℝ) / A *
        (1 / primePoolHarmonicMass A (2 * A)) := by ring
    _ ≤ ((primeProgressionWindow q a A A).card : ℝ) / A *
        (8 * Real.log (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = 8 * (Real.log (A : ℝ) / A) * ((primeProgressionWindow q a A A).card : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

end Hindman168
