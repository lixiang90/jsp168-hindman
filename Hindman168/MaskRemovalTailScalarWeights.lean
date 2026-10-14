import Hindman168.MaskRemovalOffDiagonalAbsorption
import Hindman168.RationalDivisorMasks

/-! Actual fresh-pool primes are units of every original tail divisor.
Multiplication and admissible integer division therefore preserve the
original row-divisor mask, without renormalizing its finite mass. -/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

theorem integerDivisorMask_unit_divided (ρ : Mass ℕ) (p : ℕ) (z : ℤ)
    (hdiv : (p : ℤ) ∣ z) (hunit : ∀ d ∈ ρ.support, p.Coprime d) :
    integerDivisorMask ρ (z / (p : ℤ)) = integerDivisorMask ρ z := by
  have he : (p : ℤ) * (z / (p : ℤ)) = z := by
    simpa only [mul_comm] using Int.ediv_mul_cancel hdiv
  calc
    _ = integerDivisorMask ρ ((p : ℤ) * (z / (p : ℤ))) :=
      (integerDivisorMask_unit_scaled ρ p _ hunit).symm
    _ = _ := by rw [he]

theorem MasterParameterConditions.pool_prime_eventually_gt_auxiliary
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F) (gap : ℕ → Fin N) :
    ∀ᶠ w in atTop, ∀ p ∈ primePool (F.pool w (gap w).val).lower
      (F.pool w (gap w).val).upper, F.auxiliary w (gap w).val < p := by
  have hd := PowerDominates.finite_choice (fun i : Fin N => hF.pool_lower_growth i.val) gap
  filter_upwards [hd.eventually_bound
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.pool w (gap w).val).lower))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.auxiliary w (gap w).val)))
    1 (by norm_num : (0 : ℝ) < 2)] with w hw
  simp only [pow_one] at hw
  have hp : (0 : ℝ) < F.auxiliary w (gap w).val := by
    exact_mod_cast (by have h := F.auxiliary_ge_two w (gap w).val; omega :
      0 < F.auxiliary w (gap w).val)
  have hlt : F.auxiliary w (gap w).val < (F.pool w (gap w).val).lower := by
    exact_mod_cast (show (F.auxiliary w (gap w).val : ℝ) <
      (F.pool w (gap w).val).lower by linarith)
  exact fun p hpool => hlt.trans_le (primePool_mem.mp hpool).1

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include hC htail in
theorem maskTail_fresh_prime_units :
    ∀ᶠ w in atTop, ∀ col,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ d ∈ (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)).support,
        p.Coprime d := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [hF.raw_cutoffs_valid, htail, hF.pool_prime_eventually_gt_auxiliary gap] with w hv ht hp
  intro col p hpool d hd
  have hc := chain_tailCutoffs_valid (C w) ((maskGeneratedMaster m gap).cutoff w)
    (primorial w) (hC w) (fun j hj => ⟨(hv j hj).1, (hv j hj).2.1⟩) col
  have hs := tailMass_support ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col) hc d hd
  exact large_prime_coprime_bounded (primePool_mem.mp hpool).2.2 (hp p hpool) hs.1
    (hs.2.1.trans (hF.chain_tail_budget_at_gap (C w) w col (gap w).val (ht col)))

include hC htail in
theorem maskTail_divisorMask_prime_scaled :
    ∀ᶠ w in atTop, ∀ col,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ z : ℤ,
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col))
        ((p : ℤ) * z) =
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)) z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  exact fun col p hp z => integerDivisorMask_unit_scaled _ p z (hu col p hp)

include hC htail in
theorem maskTail_divisorMask_pair_scaled :
    ∀ᶠ w in atTop, ∀ col,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper,
      ∀ q ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ z : ℤ,
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col))
        (((p*q : ℕ) : ℤ) * z) =
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)) z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  intro col p hp q hq z
  exact integerDivisorMask_unit_scaled _ (p*q) z (fun d hd =>
    (hu col p hp d hd).mul_left (hu col q hq d hd))

include hC htail in
theorem maskTail_divisorMask_prime_divided :
    ∀ᶠ w in atTop, ∀ col,
      ∀ p ∈ primePool ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper, ∀ z : ℤ, (p : ℤ) ∣ z →
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col))
        (z / (p : ℤ)) =
      integerDivisorMask (tailMass (primorial w) ((C w).tailCutoffs ((maskGeneratedMaster m gap).cutoff w) col)) z := by
  filter_upwards [maskTail_fresh_prime_units gap C hC htail] with w hu
  exact fun col p hp z hz => integerDivisorMask_unit_divided _ p z hz (hu col p hp)

end Hindman168
