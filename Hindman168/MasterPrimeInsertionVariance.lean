import Hindman168.PrimeInsertionMoments

/-! Actual master scales make the pool-divisor centered variance smaller
than every inverse power of the earlier gap auxiliary budget. The
endpoint-squared residue cap controls both single and pair moduli. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPrimeInsertionResidueCap (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (w : ℕ) : ℝ :=
  |residueError (F.cutoff w (pivot w).val) (primorial w)
    (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2)|

noncomputable def masterPrimeInsertionVarianceCap (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (w : ℕ) : ℝ :=
  ((F.pool w (gap w).val).harmonicMass)⁻¹ +
    (3 + ((F.pool w (gap w).val).harmonicMass)⁻¹) * masterPrimeInsertionResidueCap F gap pivot w

theorem masterPoolPrime_pair_budget (F : MasterParameterFamily) {N : ℕ}
    (gap : ℕ → Fin N) (w : ℕ) {p q : ℕ}
    (hp : p ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper)
    (hq : q ∈ primePool (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper) :
    p ≤ ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2 ∧
      q ≤ ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2 ∧
      p * q ≤ ((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2 := by
  let K := (F.pool w (gap w).val).upper + F.auxiliary w (gap w).val
  have haux := F.auxiliary_ge_two w (gap w).val
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hpK : p ≤ K := by have h := (primePool_mem.mp hp).2.1; dsimp [K]; omega
  have hqK : q ≤ K := by have h := (primePool_mem.mp hq).2.1; dsimp [K]; omega
  have hsq : K ≤ K ^ 2 := by nlinarith
  exact ⟨hpK.trans hsq, hqK.trans hsq, by simpa only [pow_two] using Nat.mul_le_mul hpK hqK⟩

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N)
  (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF in
theorem MasterParameterConditions.pool_harmonic_inverse_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ))
      (fun w => ((F.pool w (gap w).val).harmonicMass)⁻¹) := by
  have hd := PowerDominates.finite_choice (fun i : Fin N => hF.pool_mass_growth i.val) gap
  apply rapid_of_polynomial_majorant hd
    (Eventually.of_forall (fun w => hF.pool_positive_mass w (gap w).val))
    (Eventually.of_forall (fun w => ⟨by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        1 ≤ F.auxiliary w (gap w).val), le_rfl⟩)) 0 (by norm_num : (0 : ℝ) < 1)
  exact Eventually.of_forall (fun w => by
    rw [abs_of_pos (inv_pos.mpr (hF.pool_positive_mass w (gap w).val))]
    simp only [pow_zero, one_mul, one_div, le_refl])

include hF horder in
theorem MasterParameterConditions.prime_insertion_residue_cap_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ))
      (masterPrimeInsertionResidueCap F gap pivot) := by
  have he := residueError_rapid
    (powerDominates_log_to_cutoff (hF.earlier_pool_power_affine_log_growth gap pivot 2 horder))
    (Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w (gap w).val; omega))
  apply he.of_abs_le
  exact Eventually.of_forall (fun w => by rw [masterPrimeInsertionResidueCap, abs_abs])

include hF in
theorem masterPrimeInsertionVarianceCap_nonneg (w : ℕ) :
    0 ≤ masterPrimeInsertionVarianceCap F gap pivot w := by
  unfold masterPrimeInsertionVarianceCap masterPrimeInsertionResidueCap
  positivity [hF.pool_positive_mass w (gap w).val]

include hF horder in
theorem MasterParameterConditions.prime_insertion_variance_cap_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ))
      (masterPrimeInsertionVarianceCap F gap pivot) := by
  have hi := hF.pool_harmonic_inverse_rapid gap
  have hr := hF.prime_insertion_residue_cap_rapid gap pivot horder
  have hsum : RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ)) (fun w =>
      ((F.pool w (gap w).val).harmonicMass)⁻¹ + 4 * masterPrimeInsertionResidueCap F gap pivot w) :=
    fun C => (hi C).add ((hr C).const_mul_left 4)
  apply hsum.of_abs_le
  filter_upwards [hi.eventually_abs_le_one] with w hw
  have hinv := (inv_pos.mpr (hF.pool_positive_mass w (gap w).val)).le
  rw [abs_of_nonneg hinv] at hw
  have hres : 0 ≤ masterPrimeInsertionResidueCap F gap pivot w := abs_nonneg _
  have hmaj : 0 ≤ ((F.pool w (gap w).val).harmonicMass)⁻¹ +
      4 * masterPrimeInsertionResidueCap F gap pivot w :=
    add_nonneg hinv (mul_nonneg (by norm_num) hres)
  rw [abs_of_nonneg (masterPrimeInsertionVarianceCap_nonneg hF gap pivot w), abs_of_nonneg hmaj]
  have hcoef : 3 + ((F.pool w (gap w).val).harmonicMass)⁻¹ ≤ 4 := by linarith
  have hp := mul_le_mul_of_nonneg_right hcoef hres
  unfold masterPrimeInsertionVarianceCap
  linarith

include hF in
theorem MasterParameterConditions.prime_insertion_variance_eventually_bound :
    ∀ᶠ w in atTop, primePoolCenteredVariance (F.pool w (gap w).val).lower
      (F.pool w (gap w).val).upper (F.cutoff w (pivot w).val) (primorial w) ≤
        masterPrimeInsertionVarianceCap F gap pivot w := by
  filter_upwards [hF.raw_cutoffs_valid, hF.pool_eventually_primorial_units gap] with w hv hu
  have hvalid := hv (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hb := primePoolCenteredVariance_bound (hF.pool_positive_mass w (gap w).val) hvalid.1
    (primorial_pos w) hvalid.2.1 (fun p hp => ⟨(masterPoolPrime_pair_budget F gap w hp hp).1, hu p hp⟩)
    (fun p hp q hq => (masterPoolPrime_pair_budget F gap w hp hq).2.2)
  have hc : (0 : ℝ) ≤ 3 + ((F.pool w (gap w).val).harmonicMass)⁻¹ := by
    positivity [hF.pool_positive_mass w (gap w).val]
  have he := mul_le_mul_of_nonneg_left (le_abs_self (residueError
    (F.cutoff w (pivot w).val) (primorial w)
    (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2))) hc
  change primePoolCenteredVariance (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper
    (F.cutoff w (pivot w).val) (primorial w) ≤ ((F.pool w (gap w).val).harmonicMass)⁻¹ +
      (3 + ((F.pool w (gap w).val).harmonicMass)⁻¹) * residueError (F.cutoff w (pivot w).val)
        (primorial w) (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 2) at hb
  unfold masterPrimeInsertionVarianceCap masterPrimeInsertionResidueCap
  linarith

include hF horder in
theorem MasterParameterConditions.prime_insertion_variance_weighted_cap_tendsto (B : ℕ) :
    Tendsto (fun w => (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimeInsertionVarianceCap F gap pivot w)
      atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using ((hF.prime_insertion_variance_cap_rapid gap pivot horder).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        0 < F.auxiliary w (gap w).val))) B) 0

end Hindman168
