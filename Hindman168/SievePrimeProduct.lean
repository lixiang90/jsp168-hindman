import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve

/-!
# The actual prime product and reciprocal density for an AP interval sieve

The sieving primes are all primes up to z except the modulus prime q.
Every retained squarefree integer up to z divides their actual product.
The density d -> 1/d is a multiplicative arithmetic function, with the
required strict prime inequalities proved unconditionally.
-/

namespace Hindman168

open scoped BigOperators Classical

def sievePrimeProduct (q z : ℕ) : ℕ := ∏ p ∈ (Nat.primesLE z).erase q, p

theorem sievePrimeProduct_dvd_primorial (q z : ℕ) :
    sievePrimeProduct q z ∣ primorial z := by
  rw [sievePrimeProduct, primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)

theorem sievePrimeProduct_squarefree (q z : ℕ) : Squarefree (sievePrimeProduct q z) :=
  (squarefree_primorial z).squarefree_of_dvd (sievePrimeProduct_dvd_primorial q z)

theorem sievePrimeProduct_ne_zero (q z : ℕ) : sievePrimeProduct q z ≠ 0 :=
  (sievePrimeProduct_squarefree q z).ne_zero

theorem squarefree_dvd_sievePrimeProduct {q z d : ℕ} (hd : Squarefree d)
    (hdz : d ≤ z) (hqd : ¬ q ∣ d) : d ∣ sievePrimeProduct q z := by
  have hs : d.primeFactors ⊆ (Nat.primesLE z).erase q := by
    intro p hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpq : p ≠ q := by intro he; subst p; exact hqd hpd
    exact Finset.mem_erase.mpr ⟨hpq, Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) hpd).trans hdz,
        Nat.prime_of_mem_primeFactors hp⟩⟩
  rw [← Nat.prod_primeFactors_of_squarefree hd, sievePrimeProduct]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hs

theorem prime_coprime_sievePrimeProduct {q : ℕ} (hq : q.Prime) (z : ℕ) :
    q.Coprime (sievePrimeProduct q z) := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  rw [sievePrimeProduct, hq.prime.dvd_finsetProd_iff] at hd
  obtain ⟨p, hp, hqp⟩ := hd
  have hpp := Nat.prime_of_mem_primesLE (Finset.mem_erase.mp hp).2
  have he : q = p := (Nat.dvd_prime hpp).mp hqp |>.resolve_left hq.ne_one
  exact (Finset.mem_erase.mp hp).1 he.symm

noncomputable def reciprocalSieveDensity : ArithmeticFunction ℝ where
  toFun d := (d : ℝ)⁻¹
  map_zero' := by simp

theorem reciprocalSieveDensity_apply (d : ℕ) :
    reciprocalSieveDensity d = (d : ℝ)⁻¹ := rfl

theorem reciprocalSieveDensity_multiplicative : reciprocalSieveDensity.IsMultiplicative := by
  refine ⟨by simp [reciprocalSieveDensity], ?_⟩
  intro m n _
  simp only [reciprocalSieveDensity_apply, Nat.cast_mul, mul_inv]

theorem reciprocalSieveDensity_prime_pos {p : ℕ} (hp : p.Prime) :
    0 < reciprocalSieveDensity p := inv_pos.mpr (by exact_mod_cast hp.pos)

theorem reciprocalSieveDensity_prime_lt_one {p : ℕ} (hp : p.Prime) :
    reciprocalSieveDensity p < 1 := by
  change (p : ℝ)⁻¹ < 1
  rw [inv_lt_one₀ (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  exact_mod_cast hp.one_lt

end Hindman168
