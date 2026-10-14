import Hindman168.MasterPrimeDiagonalSampling

/-! Absorbing the two distinct fresh-prime divisor multipliers by the
actual harmonic dilation. The original comparison mass is unnormalized.
The bound is uniform over all primes in the actual pool and all tests
with a fixed polynomial sup bound at the earlier gap budget. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem primeDivisorEta_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (z : ℤ) :
    primeDivisorEta p z * primeDivisorEta q z = primeDivisorEta (p * q) z := by
  have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hne
  have hd : ((p * q : ℕ) : ℤ) ∣ z ↔ (p : ℤ) ∣ z ∧ (q : ℤ) ∣ z := by
    simp only [Int.natCast_dvd]
    exact ⟨fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  unfold primeDivisorEta
  simp only [hd]
  simp only [Nat.cast_mul]
  by_cases h₁ : (p : ℤ) ∣ z <;> by_cases h₂ : (q : ℤ) ∣ z <;> simp [h₁, h₂]

theorem integerEtaMass_expectation (X W k : ℕ) (f : ℤ → ℝ) :
    expectation (integerEtaMass X W k) f =
      expectation (integerMass X W) (fun z => primeDivisorEta k z * f z) := by
  have hs : (integerEtaMass X W k).support ⊆ (integerMass X W).support := by
    intro z hz
    apply Finsupp.mem_support_iff.mpr
    intro he
    have hh := Finsupp.mem_support_iff.mp hz
    rw [integerEtaMass_apply, he] at hh
    simp only [mul_zero, ite_self] at hh
    exact hh rfl
  rw [expectation_eq_sum _ _ hs]
  unfold expectation Finsupp.sum
  apply Finset.sum_congr rfl
  intro z _
  rw [integerEtaMass_apply]
  simp only [primeDivisorEta, mul_ite, ite_mul, mul_zero, zero_mul]
  split_ifs <;> ring

theorem distinctPrimeEta_product_expectation {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (X W : ℕ) (f : ℤ → ℝ) :
    expectation (integerMass X W) (fun z => primeDivisorEta p z * primeDivisorEta q z * f z) =
      expectation (integerEtaMass X W (p * q)) f := by
  simp only [primeDivisorEta_product hp hq hne, integerEtaMass_expectation]

noncomputable def masterPrimePairDilationErrorCap (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (w : ℕ) : ℝ :=
  dilationError (F.cutoff w (pivot w).val) (primorial w)
    (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2)

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N)
  (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF horder in
theorem MasterParameterConditions.prime_pair_dilation_cap_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ))
      (masterPrimePairDilationErrorCap F gap pivot) := by
  exact dilationError_rapid (hF.earlier_pool_power_affine_log_growth gap pivot 2 horder)
    (Eventually.of_forall (fun w => by
      have h := F.auxiliary_ge_two w (gap w).val
      have hp : 1 ≤ (F.pool w (gap w).val).upper + F.auxiliary w (gap w).val := by omega
      exact one_le_pow₀ hp))
    (Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w (gap w).val; omega))

include hF horder in
theorem MasterParameterConditions.distinct_prime_eta_dilation_bound (B : ℕ) :
    ∀ᶠ w in atTop, ∀ p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper,
      ∀ q ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper, p ≠ q →
      ∀ f : ℤ → ℝ, (∀ z, |f z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => primeDivisorEta p z * primeDivisorEta q z * f z) -
        expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => f (((p * q : ℕ) : ℤ) * z))| ≤
      (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w := by
  have hd := powerDominates_log_to_cutoff (hF.earlier_pool_power_affine_log_growth gap pivot 2 horder)
  filter_upwards [sampling_eventually_geometry hd, hF.raw_cutoffs_valid,
    hF.pool_eventually_primorial_units gap] with w hg hv hu
  intro p hp q hq hne f hf
  have hpP := (primePool_mem.mp hp).2.2
  have hqP := (primePool_mem.mp hq).2.2
  have hk : 0 < p * q := Nat.mul_pos hpP.pos hqP.pos
  have hkK : p * q ≤ ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2 := by
    have hpB := (primePool_mem.mp hp).2.1
    have hqB := (primePool_mem.mp hq).2.1
    have hpL : p ≤ (F.pool w (gap w).val).upper + F.auxiliary w (gap w).val := by omega
    have hqL : q ≤ (F.pool w (gap w).val).upper + F.auxiliary w (gap w).val := by omega
    simpa only [pow_two] using Nat.mul_le_mul hpL hqL
  have hco := (hu p hp).mul_right (hu q hq)
  have hvalid := hv (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hb := (integer_harmonic_dilation_error hvalid.1 (primorial_pos w) hk
    (hkK.trans hg.2.2) hco hvalid.2.1).trans (dilationError_mono hvalid.1 hk hkK hvalid.2.1)
  have he := expectation_difference_bound
    ((integerMass (F.cutoff w (pivot w).val) (primorial w)).mapDomain
      (fun z => ((p * q : ℕ) : ℤ) * z))
    (integerEtaMass (F.cutoff w (pivot w).val) (primorial w) (p * q)) f
    ((F.auxiliary w (gap w).val : ℝ) ^ B) hf
  rw [expectation_push] at he
  rw [distinctPrimeEta_product_expectation hpP hqP hne, abs_sub_comm]
  exact he.trans (mul_le_mul_of_nonneg_left hb (by positivity))

include hF horder in
theorem MasterParameterConditions.prime_pair_dilation_weighted_cap_tendsto (B : ℕ) :
    Tendsto (fun w => (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimePairDilationErrorCap F gap pivot w)
      atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using ((hF.prime_pair_dilation_cap_rapid gap pivot horder).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        0 < F.auxiliary w (gap w).val))) B) 0

include hF horder in
theorem MasterParameterConditions.distinct_prime_eta_dilation_uniform_zero (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper,
      ∀ q ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper, p ≠ q →
      ∀ f : ℤ → ℝ, (∀ z, |f z| ≤ (F.auxiliary w (gap w).val : ℝ) ^ B) →
      |expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => primeDivisorEta p z * primeDivisorEta q z * f z) -
        expectation (integerMass (F.cutoff w (pivot w).val) (primorial w))
          (fun z => f (((p * q : ℕ) : ℤ) * z))| < ε := by
  filter_upwards [hF.distinct_prime_eta_dilation_bound gap pivot horder B,
    (hF.prime_pair_dilation_weighted_cap_tendsto gap pivot horder B).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro p hp q hq hne f hf
  exact (hb p hp q hq hne f hf).trans_lt he

end Hindman168
