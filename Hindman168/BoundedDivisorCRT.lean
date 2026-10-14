import Hindman168.PrimePowerUnitExcess
import Hindman168.FiniteExcessTransfer

/-!
# Original bounded rough divisors and their exact CRT moduli

Every positive divisor is reconstructed from any finite set containing
its prime factors. For a bounded W-unit with all primes <=w dividing W,
only primes in (w,V] occur. The product of the actual row divisors is
therefore the exact prime-power CRT modulus, rather than a larger modulus.
The bound needed for the finite prime-law transfer also follows directly
from divisibility and the original divisor bound.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem primeValuationDivisor_full (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) (hn : n ≠ 0) (hcover : n.primeFactors ⊆ S) :
    primeValuationDivisor S n.factorization = n := by
  apply Nat.eq_of_factorization_eq (primeValuationDivisor_ne_zero S _ hS) hn
  intro p
  rw [primeValuationDivisor_factorization_apply S _ hS]
  by_cases hp : p ∈ S
  · simp only [if_pos hp]
  · rw [if_neg hp]
    exact (Finsupp.notMem_support_iff.mp (fun h => hp (hcover h))).symm

def boundedRoughPrimeSet (w V : ℕ) : Finset ℕ :=
  (Finset.range (V + 1)).filter (fun p => p.Prime ∧ w < p)

theorem mem_boundedRoughPrimeSet (w V p : ℕ) :
    p ∈ boundedRoughPrimeSet w V ↔ p.Prime ∧ w < p ∧ p ≤ V := by
  simp only [boundedRoughPrimeSet, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

theorem bounded_unit_primeFactors_subset (w V W n : ℕ) (hV : n ≤ V)
    (hc : n.Coprime W) (hsmall : ∀ p, p.Prime → p ≤ w → p ∣ W) :
    n.primeFactors ⊆ boundedRoughPrimeSet w V := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hpV := (Nat.le_of_mem_primeFactors hp).trans hV
  have hgreater : w < p := by
    by_contra h
    have hd : p ∣ n.gcd W := Nat.dvd_gcd hpn (hsmall p hprime (by omega))
    rw [hc.gcd_eq_one] at hd
    exact hprime.not_dvd_one hd
  exact (mem_boundedRoughPrimeSet w V p).mpr ⟨hprime, hgreater, hpV⟩

theorem actual_row_divisor_crt_modulus {q : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (d : Fin q → ℕ) (hd : ∀ u, d u ≠ 0)
    (hcover : ∀ u, (d u).primeFactors ⊆ S) :
    (∏ p : S, (p : ℕ) ^ (∑ u, (d u).factorization p)) = ∏ u, d u := by
  have hrow (u : Fin q) : (∏ p : S, (p : ℕ) ^ (d u).factorization p) = d u := by
    rw [Finset.prod_coe_sort S (fun p => p ^ (d u).factorization p)]
    exact primeValuationDivisor_full S hS (d u) (hd u) (hcover u)
  calc
    _ = ∏ u : Fin q, ∏ p : S, (p : ℕ) ^ (d u).factorization p :=
      (rowPrimePower_divisor_product (fun p : S => (p : ℕ)) q
        (fun p : S => fun u => (d u).factorization p)).symm
    _ = _ := Finset.prod_congr rfl (fun u _ => hrow u)

theorem actual_row_primePart_le {q : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (d : Fin q → ℕ) (hd : ∀ u, 0 < d u)
    (V : ℕ) (hV : ∀ u, d u ≤ V) (u : Fin q) :
    (∏ p : S, (p : ℕ) ^ (d u).factorization p) ≤ V := by
  rw [Finset.prod_coe_sort S (fun p => p ^ (d u).factorization p)]
  exact (Nat.le_of_dvd (hd u) (primeValuationDivisor_dvd S (d u).factorization hS
    (d u) (hd u).ne' (fun _ _ => le_rfl))).trans (hV u)

theorem actual_bounded_divisor_betaProduct_bound {q : ℕ} {α : Type*}
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (d : Fin q → ℕ)
    (hd : ∀ u, 0 < d u) (V : ℕ) (hV : ∀ u, d u ≤ V)
    (bad : S → α → Prop) (x : α) :
    0 ≤ localExcessBetaProduct (fun p : S => (p : ℕ))
        (fun p : S => fun u => (d u).factorization p) bad x ∧
      localExcessBetaProduct (fun p : S => (p : ℕ))
        (fun p : S => fun u => (d u).factorization p) bad x ≤ ((V ^ q : ℕ) : ℝ) := by
  letI : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(hS p p.property).ne_zero⟩
  exact localExcessBetaProduct_bounded _ _ bad V (actual_row_primePart_le S hS d hd V hV) x

end Hindman168
