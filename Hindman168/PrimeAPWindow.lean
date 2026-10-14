import Hindman168.PrimeAP

/-!
# AP-PNT on the actual half-open dyadic prime pools

Both dyadic endpoints are composite once n >= 2. This explicit condition
removes the endpoint discrepancy between the PNT's closed prefixes and
the master construction's half-open prime pools.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

noncomputable def primePoolLogResidue (q a A B : ℕ) : ℝ :=
  ∑ p ∈ primePool A B, if p % q = a then Real.log p else 0

theorem primeLogPrefix_nat_of_not_prime (q a N : ℕ) (hN : ¬ N.Prime) :
    primeLogPrefix q a (N : ℝ) = ∑ p ∈ Finset.range N,
      if p.Prime then (if p % q = a then Real.log p else 0) else 0 := by
  have hI : Finset.Iic N = insert N (Finset.range N) := by
    ext p
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_range]
    omega
  rw [primeLogPrefix, Nat.floor_natCast, Finset.sum_filter, hI,
    Finset.sum_insert (by simp)]
  simp only [if_neg hN, zero_add]

theorem primePoolLogResidue_eq_prefix {A B : ℕ} (q a : ℕ)
    (hAB : A ≤ B) (hA : ¬ A.Prime) (hB : ¬ B.Prime) :
    primePoolLogResidue q a A B = primeLogPrefix q a (B : ℝ) - primeLogPrefix q a (A : ℝ) := by
  rw [primeLogPrefix_nat_of_not_prime q a B hB,
    primeLogPrefix_nat_of_not_prime q a A hA]
  unfold primePoolLogResidue primePool
  rw [Finset.sum_filter]
  exact Finset.sum_Ico_eq_sub _ hAB

theorem primePoolLogResidue_dyadic_slice (q a n : ℕ) (hn : 2 ≤ n) :
    primePoolLogResidue q a (2 ^ n) (2 ^ (n + 1)) = primeLogDyadicSlice q a n := by
  exact primePoolLogResidue_eq_prefix q a
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    (Nat.Prime.not_prime_pow hn) (Nat.Prime.not_prime_pow (by omega))

theorem primePoolLogResidue_dyadic_div_tendsto {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    Tendsto (fun n : ℕ => primePoolLogResidue q a (2 ^ n) (2 ^ (n + 1)) / (2 ^ n : ℕ))
      atTop (𝓝 (1 / q.totient)) := by
  apply (primeLogDyadicSlice_div_tendsto hq ha haq).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [primePoolLogResidue_dyadic_slice q a n hn]

theorem primePoolLogResidue_dyadic_eventually_pos {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    ∀ᶠ n in atTop, 0 < primePoolLogResidue q a (2 ^ n) (2 ^ (n + 1)) := by
  filter_upwards [eventually_ge_atTop 2, primeLogDyadicSlice_eventually_pos hq ha haq] with n hn hp
  rwa [primePoolLogResidue_dyadic_slice q a n hn]

theorem primePoolLogResidue_pos_exists {q a A B : ℕ}
    (h : 0 < primePoolLogResidue q a A B) : ∃ p ∈ primePool A B, p % q = a := by
  by_contra hn
  push Not at hn
  have hz : primePoolLogResidue q a A B = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact if_neg (hn p hp)
  linarith

theorem primeAP_eventually_prime_in_dyadic {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) :
    ∀ᶠ n in atTop, ∃ p ∈ primePool (2 ^ n) (2 ^ (n + 1)), p % q = a :=
  (primePoolLogResidue_dyadic_eventually_pos hq ha haq).mono
    (fun _ hn => primePoolLogResidue_pos_exists hn)

theorem primeAP_uniform_eventually_prime_in_dyadic {q : ℕ} (A : Finset ℕ)
    (hq : 1 ≤ q) (hA : ∀ a ∈ A, a.Coprime q ∧ a < q) :
    ∀ᶠ n in atTop, ∀ a ∈ A, ∃ p ∈ primePool (2 ^ n) (2 ^ (n + 1)), p % q = a := by
  apply (eventually_all_finset A).mpr
  intro a ha
  exact primeAP_eventually_prime_in_dyadic hq (hA a ha).1 (hA a ha).2

end Hindman168
