import Hindman168.PrimeInsertionReplacement

/-! Prime-average insertion under the actual master harmonic law, with
an explicit vanishing error uniform in polynomially bounded tests.
Arbitrary independent outside variables retain their original law. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPrimeInsertionErrorCap (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (B w : ℕ) : ℝ :=
  Real.sqrt ((F.auxiliary w (gap w).val : ℝ) ^ (2 * B) * masterPrimeInsertionVarianceCap F gap pivot w) +
    (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N)
  (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF horder in
theorem MasterParameterConditions.prime_insertion_error_cap_tendsto (B : ℕ) :
    Tendsto (masterPrimeInsertionErrorCap F gap pivot B) atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (hF.prime_insertion_variance_weighted_cap_tendsto gap pivot horder (2 * B))
  unfold masterPrimeInsertionErrorCap
  simpa only [Function.comp_apply, Real.sqrt_zero, zero_add] using hs.add
    (hF.prime_pair_dilation_weighted_cap_tendsto gap pivot horder B)

include hF horder in
theorem MasterParameterConditions.prime_average_insertion_bound (B : ℕ) :
    ∀ᶠ w in atTop, ∀ f : ℤ → ℝ, (∀ z, |f z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (integerMass (F.cutoff w (pivot w).val) (primorial w)) f -
        expectation (primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
          (fun p => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
            (fun z => f ((p : ℤ) * z)))| ≤ masterPrimeInsertionErrorCap F gap pivot B w := by
  have hd := powerDominates_log_to_cutoff (hF.earlier_pool_power_affine_log_growth gap pivot 2 horder)
  filter_upwards [sampling_eventually_geometry hd, hF.raw_cutoffs_valid,
    hF.pool_eventually_primorial_units gap, hF.prime_insertion_variance_eventually_bound gap pivot]
    with w hg hv hu hvar
  intro f hf
  have hvalid := hv (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hb := primePool_insertion_bound (hF.pool_positive_mass w (gap w).val) hvalid.1
    (primorial_pos w) hg.2.2 hvalid.2.1
    (fun p hp => ⟨(masterPoolPrime_pair_budget F gap w hp hp).1, hu p hp⟩) (by positivity) f hf
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar)
    (pow_nonneg (Nat.cast_nonneg (F.auxiliary w (gap w).val)) B)
  have he : (F.auxiliary w (gap w).val : ℝ) ^ B * Real.sqrt (masterPrimeInsertionVarianceCap F gap pivot w) =
      Real.sqrt ((F.auxiliary w (gap w).val : ℝ) ^ (2 * B) * masterPrimeInsertionVarianceCap F gap pivot w) := by
    rw [show 2 * B = B * 2 by omega, pow_mul, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) B)]
  unfold masterPrimeInsertionErrorCap
  exact (hb.trans (add_le_add hs le_rfl)).trans_eq (by rw [he]; rfl)

include hF horder in
theorem MasterParameterConditions.prime_average_insertion_uniform_zero (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ f : ℤ → ℝ, (∀ z, |f z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (integerMass (F.cutoff w (pivot w).val) (primorial w)) f -
        expectation (primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
          (fun p => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
            (fun z => f ((p : ℤ) * z)))| < ε := by
  filter_upwards [hF.prime_average_insertion_bound gap pivot horder B,
    (hF.prime_insertion_error_cap_tendsto gap pivot horder B).eventually (eventually_lt_nhds hε)]
    with w hb he
  intro f hf
  exact (hb f hf).trans_lt he

include hF horder in
theorem MasterParameterConditions.prime_average_insertion_outside_bound {ι : Type*} (B : ℕ) :
    ∀ᶠ w in atTop, ∀ ρ : Mass ι, (∀ r, 0 ≤ ρ r) → total ρ = 1 →
      ∀ f : ι → ℤ → ℝ,
      (∀ r ∈ ρ.support, ∀ z, |f r z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w)) (f r)) -
        expectation ρ (fun r =>
          expectation (primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
            (fun p => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
              (fun z => f r ((p : ℤ) * z))))| ≤ masterPrimeInsertionErrorCap F gap pivot B w := by
  filter_upwards [hF.prime_average_insertion_bound gap pivot horder B] with w hb
  intro ρ hρ ht f hf
  have he := expectation_difference_support_bound ρ hρ
    (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w)) (f r))
    (fun r => expectation (primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
      (fun p => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
        (fun z => f r ((p : ℤ) * z)))) (masterPrimeInsertionErrorCap F gap pivot B w)
    (fun r hr => hb (f r) (hf r hr))
  simpa only [ht, one_mul] using he

include hF horder in
theorem MasterParameterConditions.prime_average_insertion_outside_uniform_zero {ι : Type*}
    (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ ρ : Mass ι, (∀ r, 0 ≤ ρ r) → total ρ = 1 →
      ∀ f : ι → ℤ → ℝ,
      (∀ r ∈ ρ.support, ∀ z, |f r z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation ρ (fun r => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w)) (f r)) -
        expectation ρ (fun r =>
          expectation (primePoolMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
            (fun p => expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
              (fun z => f r ((p : ℤ) * z))))| < ε := by
  filter_upwards [hF.prime_average_insertion_outside_bound (ι := ι) gap pivot horder B,
    (hF.prime_insertion_error_cap_tendsto gap pivot horder B).eventually (eventually_lt_nhds hε)]
    with w hb he
  intro ρ hρ ht f hf
  exact (hb ρ hρ ht f hf).trans_lt he

end Hindman168
