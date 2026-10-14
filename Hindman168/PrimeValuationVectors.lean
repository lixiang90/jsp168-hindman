import Hindman168.PowerUnitEulerFactors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Extracting a finite vector of actual prime valuations

The divisor built from the specified prime powers has exactly the specified
finite valuation vector. Every positive integer with this vector uniquely
has that divisor removed, leaving a number coprime to the specified primes.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def primeValuationDivisor (S : Finset ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ p ∈ S, p ^ a p

theorem primeValuationDivisor_ne_zero (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) : primeValuationDivisor S a ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)

theorem primeValuationDivisor_factorization (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (primeValuationDivisor S a).factorization = ∑ p ∈ S, Finsupp.single p (a p) := by
  rw [primeValuationDivisor, Nat.factorization_prod
    (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)]
  exact Finset.sum_congr rfl (fun p hp => (hS p hp).factorization_pow)

theorem primeValuationDivisor_factorization_apply (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (p : ℕ) :
    (primeValuationDivisor S a).factorization p = if p ∈ S then a p else 0 := by
  classical
  rw [primeValuationDivisor_factorization S a hS]
  simp [Finsupp.single_apply]

theorem primeValuationDivisor_coprime (S : Finset ℕ) (a : ℕ → ℕ) (W : ℕ)
    (hc : ∀ p ∈ S, p.Coprime W) : (primeValuationDivisor S a).Coprime W := by
  exact Nat.Coprime.prod_left (fun p hp => (hc p hp).pow_left _)

theorem primeValuationDivisor_dvd (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) (hn : n ≠ 0)
    (ha : ∀ p ∈ S, a p ≤ n.factorization p) : primeValuationDivisor S a ∣ n := by
  apply (Nat.factorization_le_iff_dvd (primeValuationDivisor_ne_zero S a hS) hn).mp
  intro p
  rw [primeValuationDivisor_factorization_apply S a hS p]
  split_ifs with hp
  · exact ha p hp
  · exact Nat.zero_le _

theorem primeValuationDivisor_mul_exact_iff (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (m : ℕ) (hm : m ≠ 0) :
    (∀ p ∈ S, (primeValuationDivisor S a * m).factorization p = a p) ↔
      m.Coprime (∏ p ∈ S, p) := by
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro hv p hp
    have hzero : m.factorization p = 0 := by
      have h := hv p hp
      rw [Nat.factorization_mul (primeValuationDivisor_ne_zero S a hS) hm,
        Finsupp.add_apply, primeValuationDivisor_factorization_apply S a hS p,
        if_pos hp] at h
      omega
    rw [Nat.coprime_comm, (hS p hp).coprime_iff_not_dvd]
    intro hd
    have h := ((hS p hp).dvd_iff_one_le_factorization hm).mp hd
    omega
  · intro hc p hp
    have hnot : ¬p ∣ m := (hS p hp).coprime_iff_not_dvd.mp (hc p hp).symm
    rw [Nat.factorization_mul (primeValuationDivisor_ne_zero S a hS) hm,
      Finsupp.add_apply, primeValuationDivisor_factorization_apply S a hS p,
      if_pos hp, Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]

theorem exists_coprime_remainder_of_valuations (S : Finset ℕ) (a : ℕ → ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) (hn : n ≠ 0)
    (ha : ∀ p ∈ S, n.factorization p = a p) :
    ∃ m : ℕ, n = primeValuationDivisor S a * m ∧ m ≠ 0 ∧
      m.Coprime (∏ p ∈ S, p) := by
  obtain ⟨m, hm⟩ := primeValuationDivisor_dvd S a hS n hn
    (fun p hp => (ha p hp).ge)
  have hm0 : m ≠ 0 := by intro hz; simp [hz] at hm; exact hn hm
  exact ⟨m, hm, hm0, (primeValuationDivisor_mul_exact_iff S a hS m hm0).mp
    (fun p hp => hm ▸ ha p hp)⟩

end Hindman168
