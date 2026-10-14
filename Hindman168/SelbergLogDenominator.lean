import Hindman168.PrimeOmittedHarmonic
import Hindman168.SievePrimeProduct
import Hindman168.SelbergRemainder
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A logarithmic lower bound for the actual truncated sieve denominator

Each Selberg term dominates its density. For density 1/d and the product
of all primes up to z except q, every q-free squarefree d <= z occurs in
the denominator. The previous harmonic estimates therefore give the
uniform lower bound log(z+1)/4, independently of q.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem selbergTerms_ge_density (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d ≤ s.selbergTerms d := by
  rw [s.selbergTerms_apply]
  have hp : 1 ≤ ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
    apply Finset.one_le_prod
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hd
    have hpos := s.nu_pos_of_prime p hpp hpP
    have hlt := s.nu_lt_one_of_prime p hpp hpP
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.mpr hlt)).mpr
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (s.nu_pos_of_dvd_prodPrimes hd).le

theorem selbergDenominator_log_lower_of_coverage (s : BoundingSieve) {q z : ℕ}
    (hq : q.Prime)
    (hnu : ∀ d, d ∣ s.prodPrimes → s.nu d = (d : ℝ)⁻¹)
    (hcover : ∀ d, Squarefree d → d ≤ z → ¬ q ∣ d → d ∣ s.prodPrimes) :
    Real.log (z + 1 : ℕ) / 4 ≤ selbergDenominator s z := by
  have hs : primeOmittedSquarefreeWindow q z ⊆ selbergDivisorWindow s z := by
    intro d hd
    obtain ⟨hds, hqd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdi, hsf⟩ := Finset.mem_filter.mp hds
    have hdz := (Finset.mem_Icc.mp hdi).2
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hcover d hsf hdz hqd, s.prodPrimes_ne_zero⟩, hdz⟩
  calc
    _ ≤ primeOmittedHarmonic q z := primeOmittedHarmonic_log_lower hq z
    _ ≤ ∑ d ∈ selbergDivisorWindow s z, (d : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun d _ _ => by positivity)
    _ ≤ selbergDenominator s z := by
      apply Finset.sum_le_sum
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [← hnu d hdP]
      exact selbergTerms_ge_density s hdP

theorem selbergDenominator_sievePrimeProduct_log_lower (s : BoundingSieve) {q z : ℕ}
    (hq : q.Prime) (hP : s.prodPrimes = sievePrimeProduct q z)
    (hnu : s.nu = reciprocalSieveDensity) :
    Real.log (z + 1 : ℕ) / 4 ≤ selbergDenominator s z := by
  apply selbergDenominator_log_lower_of_coverage s hq
  · intro d _
    rw [hnu, reciprocalSieveDensity_apply]
  · intro d hd hdz hqd
    rw [hP]
    exact squarefree_dvd_sievePrimeProduct hd hdz hqd

theorem siftedSum_le_logarithmic_sieve (s : BoundingSieve) {q z : ℕ}
    (hq : q.Prime) (hz : 1 ≤ z) (hP : s.prodPrimes = sievePrimeProduct q z)
    (hnu : s.nu = reciprocalSieveDensity) (hX : 0 ≤ s.totalMass)
    {E : ℝ} (hE : 0 ≤ E) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ E) :
    s.siftedSum ≤ 4 * s.totalMass / Real.log (z + 1 : ℕ) + E * (z : ℝ) ^ 4 := by
  have hlog : 0 < Real.log (z + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hden := selbergDenominator_sievePrimeProduct_log_lower s hq hP hnu
  have hweight : ∀ d, d ∣ s.prodPrimes → d ≤ z → (s.nu d)⁻¹ ≤ (d : ℝ) := by
    intro d _ _
    simp only [hnu, reciprocalSieveDensity_apply, inv_inv, le_refl]
  have hm : s.totalMass / selbergDenominator s z ≤
      s.totalMass / (Real.log (z + 1 : ℕ) / 4) :=
    div_le_div_of_nonneg_left hX (div_pos hlog (by norm_num)) hden
  calc
    _ ≤ s.totalMass / selbergDenominator s z + E * (z : ℝ) ^ 4 :=
      siftedSum_le_selberg_uniform_remainder s hz hweight hE hrem
    _ ≤ s.totalMass / (Real.log (z + 1 : ℕ) / 4) + E * (z : ℝ) ^ 4 :=
      add_le_add hm le_rfl
    _ = _ := by ring

end Hindman168
