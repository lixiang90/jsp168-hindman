import Hindman168.MasterPrimeInsertionVariance

/-! Explicit L2 replacement and averaged dilation for the actual pool
mask. The square root is taken only after the original centered variance
has been computed. The comparison divisor law is never normalized. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem primePoolDivisorMask_product_expectation (A B X W : ℕ) (f : ℤ → ℝ) :
    expectation (integerMass X W) (fun z => primePoolDivisorMask A B z * f z) =
      expectation (primePoolMass A B) (fun p => expectation (integerEtaMass X W p) f) := by
  have he (z : ℤ) : primePoolDivisorMask A B z * f z =
      expectation (primePoolMass A B) (fun p => primeDivisorEta p z * f z) := by
    unfold primePoolDivisorMask
    have hh := expectation_const_mul (primePoolMass A B) (f z) (fun p => primeDivisorEta p z)
    have hcomm : (fun p => f z * primeDivisorEta p z) = fun p => primeDivisorEta p z * f z := by
      funext p
      ring
    rw [hcomm] at hh
    linarith
  simp_rw [he]
  rw [expectation_comm]
  simp only [← integerEtaMass_expectation]

theorem primePool_centered_replacement_bound {A B X W : ℕ}
    (hZ : 0 < harmonicNormalizer X W) {R : ℝ} (hR : 0 ≤ R)
    (f : ℤ → ℝ) (hf : ∀ z ∈ (integerMass X W).support, |f z| ≤ R) :
    |expectation (integerMass X W) (fun z => primePoolDivisorMask A B z * f z) -
      expectation (integerMass X W) f| ≤ R * Real.sqrt (primePoolCenteredVariance A B X W) := by
  let e := expectation (integerMass X W) (fun z => f z * (primePoolDivisorMask A B z - 1))
  have he : e = expectation (integerMass X W) (fun z => primePoolDivisorMask A B z * f z) -
      expectation (integerMass X W) f := by
    dsimp [e]
    rw [expectation_centered_product_eq]
    have hh : (fun z => f z * primePoolDivisorMask A B z) =
        fun z => primePoolDivisorMask A B z * f z := by funext z; ring
    rw [hh, one_mul]
  have hc := finite_weighted_cauchy_schwarz (integerMass X W) (integerMass_nonneg hZ)
    f (fun _ => R) (fun z => primePoolDivisorMask A B z - 1) hf
  rw [expectation_const, integerMass_total hZ, one_mul, expectation_const_mul] at hc
  change |e| ^ 2 ≤ R * (R * primePoolCenteredVariance A B X W) at hc
  have hs := Real.sqrt_le_sqrt hc
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg R)] at hs
  simpa only [Real.sqrt_sq_eq_abs, abs_abs, abs_of_nonneg hR, he] using hs

theorem primePool_dilation_comparison_bound {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hKX : K ≤ X) (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p)
    {R : ℝ} (hR : 0 ≤ R) (f : ℤ → ℝ) (hf : ∀ z, |f z| ≤ R) :
    |expectation (primePoolMass A B) (fun p => expectation (integerMass X W) (fun z => f ((p : ℤ) * z))) -
      expectation (integerMass X W) (fun z => primePoolDivisorMask A B z * f z)| ≤ R * dilationError X W K := by
  rw [primePoolDivisorMask_product_expectation]
  have ht := primePoolMass_total hS
  have hb := expectation_difference_support_bound (primePoolMass A B) (primePoolMass_nonneg A B)
    (fun p => expectation (integerMass X W) (fun z => f ((p : ℤ) * z)))
    (fun p => expectation (integerEtaMass X W p) f) (R * dilationError X W K) (fun p hp => by
      have hpool := primePoolMass_support A B hp
      have hk := (primePool_mem.mp hpool).2.2.pos
      have hd := (integer_harmonic_dilation_error hX hW hk ((hs p hpool).1.trans hKX)
        (hs p hpool).2 hlog).trans (dilationError_mono hX hk (hs p hpool).1 hlog)
      have he := expectation_difference_bound ((integerMass X W).mapDomain (fun z => (p : ℤ) * z))
        (integerEtaMass X W p) f R hf
      rw [expectation_push] at he
      exact he.trans (mul_le_mul_of_nonneg_left hd hR))
  simpa only [ht, one_mul] using hb

theorem primePool_insertion_bound {A B X W K : ℕ}
    (hS : 0 < primePoolHarmonicMass A B) (hX : 2 ≤ X) (hW : 0 < W)
    (hKX : K ≤ X) (hlog : (W : ℝ) / X < Real.log X)
    (hs : ∀ p ∈ primePool A B, p ≤ K ∧ W.Coprime p)
    {R : ℝ} (hR : 0 ≤ R) (f : ℤ → ℝ) (hf : ∀ z, |f z| ≤ R) :
    |expectation (integerMass X W) f -
      expectation (primePoolMass A B) (fun p => expectation (integerMass X W) (fun z => f ((p : ℤ) * z)))| ≤
      R * Real.sqrt (primePoolCenteredVariance A B X W) + R * dilationError X W K := by
  have hc := primePool_centered_replacement_bound (A := A) (B := B)
    (harmonicNormalizer_pos hX hW hlog) hR f (fun z _ => hf z)
  have hd := primePool_dilation_comparison_bound hS hX hW hKX hlog hs hR f hf
  have ht := abs_sub_le (expectation (integerMass X W) f)
    (expectation (integerMass X W) (fun z => primePoolDivisorMask A B z * f z))
    (expectation (primePoolMass A B) (fun p => expectation (integerMass X W) (fun z => f ((p : ℤ) * z))))
  exact ht.trans (add_le_add (by rw [abs_sub_comm]; exact hc) (by rw [abs_sub_comm]; exact hd))

end Hindman168
