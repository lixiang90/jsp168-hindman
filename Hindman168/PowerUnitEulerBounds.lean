import Hindman168.PrimeValuationVectors
import Hindman168.HarmonicSampling

/-!
# Uniform bounds for the finite Euler normalization

For any finite distinct prime set, the ratio between its Euler factors at
s>1 and at s=1 is between 1 and W^(s-1), where W is the prime product.
The factors at one equal the original harmonic unit density.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem primeProduct_primeFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).primeFactors = S := by
  have he : primeValuationDivisor S (fun _ => 1) = ∏ p ∈ S, p := by
    simp [primeValuationDivisor]
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff,
    ← he, primeValuationDivisor_factorization_apply S (fun _ => 1) hS p]
  by_cases hp : p ∈ S <;> simp [hp]

theorem unitDensity_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    unitDensity (∏ p ∈ S, p) = ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  have hn : (∏ p ∈ S, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hQ := Nat.totient_eq_mul_prod_factors (∏ p ∈ S, p)
  have hR : ((∏ p ∈ S, p).totient : ℝ) =
      (∏ p ∈ S, p : ℕ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hQ
    push_cast at h
    rw [primeProduct_primeFactors S hS] at h
    simpa only [Nat.cast_prod] using h
  unfold unitDensity
  rw [hR]
  field_simp [show ((∏ p ∈ S, p : ℕ) : ℝ) ≠ 0 from by exact_mod_cast hn]

theorem prime_euler_factor_bounds {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : 2 ≤ p) :
    1 - (p : ℝ)⁻¹ ≤ 1 - (p : ℝ) ^ (-s) ∧
      1 - (p : ℝ) ^ (-s) ≤ (1 - (p : ℝ)⁻¹) * (p : ℝ) ^ (s - 1) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr : (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1 : ℝ) ≤ p) (by linarith : -s ≤ -1)
  have ht : (1 : ℝ) ≤ (p : ℝ) ^ (s - 1) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1 : ℝ) ≤ p) (by linarith : 0 ≤ s - 1)
  have ht0 : 0 < (p : ℝ) ^ (s - 1) := by linarith
  have hm : (p : ℝ) ^ (-s) * ((p : ℝ) * (p : ℝ) ^ (s - 1)) = 1 := by
    calc
      _ = ((p : ℝ) ^ (-s) * (p : ℝ) ^ (s - 1)) * (p : ℝ) := by ring
      _ = (p : ℝ) ^ (-s + (s - 1)) * (p : ℝ) := by rw [Real.rpow_add hp0]
      _ = (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) := by congr 2; ring
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hp0.ne']
  have hi : (p : ℝ)⁻¹ * (p : ℝ) = 1 := inv_mul_cancel₀ hp0.ne'
  have hpoly : 0 ≤ ((p : ℝ) ^ (s - 1) - 1) *
      (((p : ℝ) - 1) * (p : ℝ) ^ (s - 1) - 1) := by
    apply mul_nonneg (by linarith)
    nlinarith
  refine ⟨by linarith, ?_⟩
  have he : (p : ℝ) ^ (-s) = ((p : ℝ) * (p : ℝ) ^ (s - 1))⁻¹ := by
    apply (mul_right_cancel₀ (mul_pos hp0 ht0).ne')
    rw [hm, inv_mul_cancel₀ (mul_pos hp0 ht0).ne']
  rw [he]
  apply (mul_le_mul_iff_right₀ (mul_pos hp0 ht0)).mp
  have hleft : (1 - ((p : ℝ) * (p : ℝ) ^ (s - 1))⁻¹) *
      ((p : ℝ) * (p : ℝ) ^ (s - 1)) = (p : ℝ) * (p : ℝ) ^ (s - 1) - 1 := by
    field_simp
  have hright : (1 - (p : ℝ)⁻¹) * (p : ℝ) ^ (s - 1) *
      ((p : ℝ) * (p : ℝ) ^ (s - 1)) = ((p : ℝ) - 1) * ((p : ℝ) ^ (s - 1)) ^ 2 := by
    field_simp
  calc
    _ = (p : ℝ) * (p : ℝ) ^ (s - 1) - 1 := by
      simpa only [mul_comm] using hleft
    _ ≤ ((p : ℝ) - 1) * ((p : ℝ) ^ (s - 1)) ^ 2 := by nlinarith [hpoly]
    _ = _ := by simpa only [mul_comm] using hright.symm

theorem prime_euler_product_bounds {s : ℝ} (hs : 1 < s)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    unitDensity (∏ p ∈ S, p) ≤ ∏ p ∈ S, (1 - (p : ℝ) ^ (-s)) ∧
      (∏ p ∈ S, (1 - (p : ℝ) ^ (-s))) ≤
        unitDensity (∏ p ∈ S, p) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (s - 1) := by
  rw [unitDensity_prime_product S hS]
  have hbase : ∀ p ∈ S, 0 ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpR)
  constructor
  · exact Finset.prod_le_prod hbase (fun p hp => (prime_euler_factor_bounds hs (hS p hp).two_le).1)
  · have he : ((∏ p ∈ S, p : ℕ) : ℝ) ^ (s - 1) = ∏ p ∈ S, (p : ℝ) ^ (s - 1) := by
      rw [Nat.cast_prod, ← Real.finsetProd_rpow S (fun p => (p : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (s - 1)]
    rw [he, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod
      (fun p hp => ((hbase p hp).trans (prime_euler_factor_bounds hs (hS p hp).two_le).1))
      (fun p hp => (prime_euler_factor_bounds hs (hS p hp).two_le).2)

theorem powerUnitNormalizer_prime_product_bounds {s : ℝ} (hs : 1 < s)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    powerUnitNormalizer s 1 * unitDensity (∏ p ∈ S, p) ≤
        powerUnitNormalizer s (∏ p ∈ S, p) ∧
      powerUnitNormalizer s (∏ p ∈ S, p) ≤
        powerUnitNormalizer s 1 * unitDensity (∏ p ∈ S, p) *
          ((∏ p ∈ S, p : ℕ) : ℝ) ^ (s - 1) := by
  rw [powerUnitNormalizer_prime_product hs S hS, ← powerUnitNormalizer_one]
  have h := prime_euler_product_bounds hs S hS
  exact ⟨mul_le_mul_of_nonneg_left h.1 (powerUnitNormalizer_pos hs 1).le,
    (mul_le_mul_of_nonneg_left h.2 (powerUnitNormalizer_pos hs 1).le).trans_eq (mul_assoc _ _ _).symm⟩

end Hindman168
