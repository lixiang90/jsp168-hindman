import Hindman168.SelbergLogDenominator
import Hindman168.PrimeResidueAtomBounds
import Mathlib.Data.Nat.ModEq

/-!
# A location-independent Selberg sieve on an actual arithmetic interval

The support is [A,A+T), with weight 1 on the prescribed class mod q.
CRT combines that class and divisibility by each sieving divisor d into
one class mod q*d. Exact interval counting then proves remainder <= 1.
All density, support, and denominator hypotheses of the upper sieve
are proved for this concrete object.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def arithmeticIntervalSieve (q z A T a : ℕ) : BoundingSieve where
  support := Finset.Ico A (A + T)
  prodPrimes := sievePrimeProduct q z
  prodPrimes_squarefree := sievePrimeProduct_squarefree q z
  weights n := if n % q = a then 1 else 0
  weights_nonneg n := by split_ifs <;> norm_num
  totalMass := (T : ℝ) / q
  nu := reciprocalSieveDensity
  nu_mult := reciprocalSieveDensity_multiplicative
  nu_pos_of_prime p hp _ := reciprocalSieveDensity_prime_pos hp
  nu_lt_one_of_prime p hp _ := reciprocalSieveDensity_prime_lt_one hp

theorem crt_residue_divisibility {q d a : ℕ} (hqd : q.Coprime d)
    (hq : 0 < q) (hd : 0 < d) (ha : a < q) (n : ℕ) :
    d ∣ n ∧ n % q = a ↔
      n % (q * d) = (Nat.chineseRemainder hqd a 0).val := by
  let r := Nat.chineseRemainder hqd a 0
  have hr : r.val < q * d := Nat.chineseRemainder_lt_mul hqd a 0 hq.ne' hd.ne'
  have hzero : ∀ m, m ≡ 0 [MOD d] ↔ d ∣ m := fun _ => Nat.modEq_zero_iff_dvd
  have haeq : ∀ m, m ≡ a [MOD q] ↔ m % q = a := by
    intro m
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha]
  have hreq : ∀ m, m ≡ r.val [MOD q * d] ↔ m % (q * d) = r.val := by
    intro m
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hr]
  constructor
  · rintro ⟨hdn, hna⟩
    exact (hreq n).mp (Nat.chineseRemainder_modEq_unique hqd
      ((haeq n).mpr hna) ((hzero n).mpr hdn))
  · intro hn
    have hm := (hreq n).mpr hn
    exact ⟨(hzero n).mp ((hm.of_mul_left q).trans r.property.2),
      (haeq n).mp ((hm.of_mul_right d).trans r.property.1)⟩

theorem arithmeticIntervalSieve_multSum (q z A T a : ℕ) {d : ℕ}
    (hqd : q.Coprime d) (hq : 0 < q) (hd : 0 < d) (ha : a < q) :
    (arithmeticIntervalSieve q z A T a).multSum d =
      ((naturalResidueWindow A T (q * d) (Nat.chineseRemainder hqd a 0).val).card : ℝ) := by
  rw [BoundingSieve.multSum]
  have he : ∀ n ∈ Finset.Ico A (A + T),
      (if d ∣ n then (if n % q = a then (1 : ℝ) else 0) else 0) =
      (if n % (q * d) = (Nat.chineseRemainder hqd a 0).val then 1 else 0) := by
    intro n _
    have hi := crt_residue_divisibility hqd hq hd ha n
    rw [← ite_and]
    by_cases h : d ∣ n ∧ n % q = a
    · simp only [if_pos h, if_pos (hi.mp h)]
    · simp only [if_neg h, if_neg (mt hi.mpr h)]
  change (∑ n ∈ Finset.Ico A (A + T),
    if d ∣ n then (if n % q = a then (1 : ℝ) else 0) else 0) = _
  rw [Finset.sum_congr rfl he]
  simp only [naturalResidueWindow, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem arithmeticIntervalSieve_rem_le_one {q : ℕ} (hq : q.Prime)
    (z A T : ℕ) {a : ℕ} (ha : a < q) {d : ℕ}
    (hd : d ∣ sievePrimeProduct q z) :
    |(arithmeticIntervalSieve q z A T a).rem d| ≤ 1 := by
  have hqd : q.Coprime d := (prime_coprime_sievePrimeProduct hq z).of_dvd_right hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (sievePrimeProduct_ne_zero q z) hd)
  have hr : (Nat.chineseRemainder hqd a 0).val < q * d :=
    Nat.chineseRemainder_lt_mul hqd a 0 hq.ne_zero hdpos.ne'
  have hc := natural_residue_count (A := A) (T := T) (Nat.mul_pos hq.pos hdpos) hr
  rw [BoundingSieve.rem, arithmeticIntervalSieve_multSum q z A T a hqd hq.pos hdpos ha]
  change |((naturalResidueWindow A T (q * d) (Nat.chineseRemainder hqd a 0).val).card : ℝ) -
    (d : ℝ)⁻¹ * ((T : ℝ) / q)| ≤ 1
  have he : (d : ℝ)⁻¹ * ((T : ℝ) / q) = (T : ℝ) / (q * d : ℕ) := by
    push_cast
    ring
  rw [he]
  exact hc

theorem arithmeticIntervalSieve_upper {q : ℕ} (hq : q.Prime)
    {z : ℕ} (hz : 1 ≤ z) (A T : ℕ) {a : ℕ} (ha : a < q) :
    (arithmeticIntervalSieve q z A T a).siftedSum ≤
      4 * ((T : ℝ) / q) / Real.log (z + 1 : ℕ) + (z : ℝ) ^ 4 := by
  have hX : 0 ≤ (arithmeticIntervalSieve q z A T a).totalMass := by
    change (0 : ℝ) ≤ (T : ℝ) / q
    positivity
  have ht : (arithmeticIntervalSieve q z A T a).totalMass = (T : ℝ) / q := rfl
  have hr : ∀ d ∈ (arithmeticIntervalSieve q z A T a).prodPrimes.divisors,
      |(arithmeticIntervalSieve q z A T a).rem d| ≤ (1 : ℝ) := by
    intro d hd
    exact arithmeticIntervalSieve_rem_le_one hq z A T ha (Nat.dvd_of_mem_divisors hd)
  have h := siftedSum_le_logarithmic_sieve (arithmeticIntervalSieve q z A T a)
    hq hz rfl rfl hX (by norm_num : (0 : ℝ) ≤ 1) hr
  simpa only [ht, one_mul] using h

end Hindman168
