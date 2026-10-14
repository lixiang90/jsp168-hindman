import Hindman168.MasterPrimeAverageInsertion

/-! Fixed-prime harmonic transfer and independent outside parameters.
The divisor law keeps its original, unnormalized coefficients. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N)
  (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF horder in
theorem MasterParameterConditions.prime_single_eta_dilation_bound (B : ℕ) :
    ∀ᶠ w in atTop, ∀ p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper,
      ∀ f : ℤ → ℝ, (∀ z, |f z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => primeDivisorEta p z * f z) -
        expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => f ((p : ℤ) * z))| ≤
      (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w := by
  have hd := powerDominates_log_to_cutoff (hF.earlier_pool_power_affine_log_growth gap pivot 2 horder)
  filter_upwards [sampling_eventually_geometry hd, hF.raw_cutoffs_valid,
    hF.pool_eventually_primorial_units gap] with w hg hv hu
  intro p hp f hf
  have hk := (primePool_mem.mp hp).2.2.pos
  have hkK := (masterPoolPrime_pair_budget F gap w hp hp).1
  have hvalid := hv (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hb := (integer_harmonic_dilation_error hvalid.1 (primorial_pos w) hk
    (hkK.trans hg.2.2) (hu p hp) hvalid.2.1).trans
      (dilationError_mono hvalid.1 hk hkK hvalid.2.1)
  have he := expectation_difference_bound
    ((integerMass (F.cutoff w (pivot w).val) (primorial w)).mapDomain (fun z => (p : ℤ) * z))
    (integerEtaMass (F.cutoff w (pivot w).val) (primorial w) p) f
    ((F.auxiliary w (gap w).val : ℝ) ^ B) hf
  rw [expectation_push, integerEtaMass_expectation, abs_sub_comm] at he
  exact he.trans (mul_le_mul_of_nonneg_left hb (by positivity))

include hF horder in
theorem MasterParameterConditions.prime_single_eta_dilation_outside_bound {ι : Type*} (B : ℕ) :
    ∀ᶠ w in atTop, ∀ ρ : Mass ι, (∀ r, 0 ≤ ρ r) → total ρ = 1 →
      ∀ p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper,
      ∀ f : ι → ℤ → ℝ,
      (∀ r ∈ ρ.support, ∀ z, |f r z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => primeDivisorEta p z * f r z)) -
        expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => f r ((p : ℤ) * z)))| ≤
      (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w := by
  filter_upwards [hF.prime_single_eta_dilation_bound gap pivot horder B] with w hb
  intro ρ hρ ht p hp f hf
  have he := expectation_difference_support_bound ρ hρ _ _
    ((F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w)
    (fun r hr => hb p hp (f r) (hf r hr))
  simpa only [ht, one_mul] using he

include hF horder in
theorem MasterParameterConditions.distinct_prime_eta_dilation_outside_bound {ι : Type*} (B : ℕ) :
    ∀ᶠ w in atTop, ∀ ρ : Mass ι, (∀ r, 0 ≤ ρ r) → total ρ = 1 →
      ∀ p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper,
      ∀ q ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper, p ≠ q →
      ∀ f : ι → ℤ → ℝ,
      (∀ r ∈ ρ.support, ∀ z, |f r z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => primeDivisorEta p z * primeDivisorEta q z * f r z)) -
        expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => f r (((p * q : ℕ) : ℤ) * z)))| ≤
      (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w := by
  filter_upwards [hF.distinct_prime_eta_dilation_bound gap pivot horder B] with w hb
  intro ρ hρ ht p hp q hq hne f hf
  have he := expectation_difference_support_bound ρ hρ _ _
    ((F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w)
    (fun r hr => hb p hp q hq hne (f r) (hf r hr))
  simpa only [ht, one_mul] using he

end Hindman168
