import Hindman168.PrimeWeightedDiagonal
import Hindman168.MasterAffineSamplingGrowth
import Hindman168.JointSamplingAsymptotics

/-! Deleting the weighted fresh-prime diagonal under the actual master
pool and a later original harmonic pivot. All rates follow from the
master conditions; the upper endpoint is not assumed to be monotone. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def masterPrimeDiagonalErrorCap (F : MasterParameterFamily)
    {N : ℕ} (gap pivot : ℕ → Fin N) (w : ℕ) : ℝ :=
  (1 + |residueError (F.cutoff w (pivot w).val) (primorial w)
    (F.pool w (gap w).val).upper|) / (F.pool w (gap w).val).harmonicMass

variable {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
  {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
  (gap pivot : ℕ → Fin N)
  (horder : ∀ᶠ w in atTop, (gap w).val ≤ (pivot w).val)

include hF in
theorem MasterParameterConditions.pool_eventually_primorial_units :
    ∀ᶠ w in atTop, ∀ p ∈ primePool (F.pool w (gap w).val).lower
      (F.pool w (gap w).val).upper, (primorial w).Coprime p := by
  have hd := PowerDominates.finite_choice (fun i : Fin N => hF.pool_lower_growth i.val) gap
  filter_upwards [hd.eventually_bound
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.pool w (gap w).val).lower))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.auxiliary w (gap w).val)))
    1 (by norm_num : (0 : ℝ) < 2), hF.primorial_le_modulus] with w hw hW
  simp only [pow_one] at hw
  have hh : F.auxiliary w (gap w).val < (F.pool w (gap w).val).lower := by
    have hp : (0 : ℝ) < F.auxiliary w (gap w).val := by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        0 < F.auxiliary w (gap w).val)
    exact_mod_cast (show (F.auxiliary w (gap w).val : ℝ) <
      (F.pool w (gap w).val).lower by linarith)
  intro p hp
  have hpP := (primePool_mem.mp hp).2.2
  have hWp : primorial w < p :=
    lt_of_le_of_lt (hW.trans (F.modulus_le_auxiliary w (gap w).val))
      (hh.trans_le (primePool_mem.mp hp).1)
  exact (hpP.coprime_iff_not_dvd.mpr
    (fun hd => (Nat.le_of_dvd (primorial_pos w) hd).not_gt hWp)).symm

include hF horder in
theorem MasterParameterConditions.earlier_pool_upper_residue_error_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ)) (fun w =>
      residueError (F.cutoff w (pivot w).val) (primorial w) (F.pool w (gap w).val).upper) := by
  have hd := (hF.earlier_pool_power_affine_log_growth gap pivot 1 horder).mono_base 1
    (Eventually.of_forall (fun w => by
      refine ⟨Nat.cast_nonneg (samplingSize (primorial w) (F.pool w (gap w).val).upper 0
        (F.auxiliary w (gap w).val)), Nat.cast_nonneg _, ?_⟩
      rw [pow_one]
      exact_mod_cast (show samplingSize (primorial w) (F.pool w (gap w).val).upper 0
          (F.auxiliary w (gap w).val) ≤ samplingSize (primorial w)
          (((F.pool w (gap w).val).upper + F.auxiliary w (gap w).val) ^ 1) 0
          (F.auxiliary w (gap w).val) by simp only [samplingSize, pow_one]; omega)))
  exact residueError_rapid (powerDominates_log_to_cutoff hd)
    (Eventually.of_forall (fun w => by have h := F.auxiliary_ge_two w (gap w).val; omega))

include hF in
theorem masterPrimeDiagonalErrorCap_nonneg (w : ℕ) :
    0 ≤ masterPrimeDiagonalErrorCap F gap pivot w :=
  div_nonneg (by positivity) (hF.pool_positive_mass w (gap w).val).le

include hF horder in
theorem MasterParameterConditions.prime_diagonal_cap_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ))
      (masterPrimeDiagonalErrorCap F gap pivot) := by
  have hd := PowerDominates.finite_choice (fun i : Fin N => hF.pool_mass_growth i.val) gap
  apply rapid_of_polynomial_majorant hd
    (Eventually.of_forall (fun w => hF.pool_positive_mass w (gap w).val))
    (Eventually.of_forall (fun w => ⟨by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        1 ≤ F.auxiliary w (gap w).val), le_rfl⟩)) 0 (by norm_num : (0 : ℝ) < 2)
  filter_upwards [(hF.earlier_pool_upper_residue_error_rapid gap pivot horder).eventually_abs_le_one]
    with w hw
  unfold masterPrimeDiagonalErrorCap
  rw [abs_of_nonneg (div_nonneg (by positivity) (hF.pool_positive_mass w (gap w).val).le), pow_zero, mul_one]
  exact div_le_div_of_nonneg_right (by linarith) (hF.pool_positive_mass w (gap w).val).le

include hF in
theorem MasterParameterConditions.prime_diagonal_mass_eventually_bound :
    ∀ᶠ w in atTop, primeWeightedDiagonalMass (F.pool w (gap w).val).lower
      (F.pool w (gap w).val).upper (F.cutoff w (pivot w).val) (primorial w) ≤
        masterPrimeDiagonalErrorCap F gap pivot w := by
  filter_upwards [hF.raw_cutoffs_valid, hF.pool_eventually_primorial_units gap] with w hw hunit
  have hv := hw (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hb := primeWeightedDiagonalMass_bound (hF.pool_positive_mass w (gap w).val)
    hv.1 (primorial_pos w) hv.2.1 (fun p hp =>
      ⟨(primePool_mem.mp hp).2.1.le, hunit p hp⟩)
  have ha := le_abs_self (residueError (F.cutoff w (pivot w).val) (primorial w)
    (F.pool w (gap w).val).upper)
  exact hb.trans (div_le_div_of_nonneg_right (by linarith)
    (hF.pool_positive_mass w (gap w).val).le)

include hF horder in
theorem MasterParameterConditions.prime_diagonal_mass_rapid :
    RapidlySmall atTop (fun w => (F.auxiliary w (gap w).val : ℝ)) (fun w =>
      primeWeightedDiagonalMass (F.pool w (gap w).val).lower (F.pool w (gap w).val).upper
        (F.cutoff w (pivot w).val) (primorial w)) := by
  apply (hF.prime_diagonal_cap_rapid gap pivot horder).of_abs_le
  filter_upwards [hF.prime_diagonal_mass_eventually_bound gap pivot, hF.raw_cutoffs_valid]
    with w hb hw
  have hv := hw (pivot w).val (Finset.mem_range.mpr (pivot w).isLt)
  have hn : 0 ≤ primeWeightedDiagonalMass (F.pool w (gap w).val).lower
      (F.pool w (gap w).val).upper (F.cutoff w (pivot w).val) (primorial w) := by
    apply expectation_nonneg _ _ (integerMass_nonneg hv.2.2)
    intro z
    apply expectation_nonneg _ _ (tensor_nonneg _ _ (primePoolMass_nonneg _ _) (primePoolMass_nonneg _ _))
    intro pq
    split_ifs <;> positivity [primeDivisorEta_nonneg pq.1 z, primeDivisorEta_nonneg pq.2 z]
  rw [abs_of_nonneg hn, abs_of_nonneg (masterPrimeDiagonalErrorCap_nonneg hF gap pivot w)]
  exact hb

include hF horder in
theorem MasterParameterConditions.prime_diagonal_weighted_cap_tendsto (B : ℕ) :
    Tendsto (fun w => (F.auxiliary w (gap w).val : ℝ) ^ B * masterPrimeDiagonalErrorCap F gap pivot w)
      atTop (𝓝 0) := by
  apply (Asymptotics.isLittleO_one_iff ℝ).mp
  simpa only [pow_zero, inv_one] using ((hF.prime_diagonal_cap_rapid gap pivot horder).mul_power
    (Eventually.of_forall (fun w => by
      exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
        0 < F.auxiliary w (gap w).val))) B) 0

end Hindman168
