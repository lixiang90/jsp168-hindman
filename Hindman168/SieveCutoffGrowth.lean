import Hindman168.PrimeProgressionSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniform sieve cutoff below all dyadic prime endpoints

The actual integer cutoff floor(A^(1/16)) is independent of the modulus.
Its logarithm is a fixed fraction of log A, while its fourth power and
log A are bounded by A^(1/4) for sufficiently large A. These estimates
turn the interval sieve remainder into a uniform small-prime atom bound.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

noncomputable def uniformSieveCutoff (A : ℕ) : ℕ := ⌊(A : ℝ) ^ (1 / 16 : ℝ)⌋₊

theorem uniformSieveCutoff_eventually :
    ∀ᶠ A : ℕ in atTop,
      2 ≤ A ∧ 1 ≤ uniformSieveCutoff A ∧ uniformSieveCutoff A < A ∧
      Real.log (A : ℝ) ≤ 32 * Real.log (uniformSieveCutoff A + 1 : ℕ) ∧
      (uniformSieveCutoff A : ℝ) ^ 4 ≤ (A : ℝ) ^ (1 / 4 : ℝ) ∧
      Real.log (A : ℝ) ≤ (A : ℝ) ^ (1 / 4 : ℝ) := by
  have ht : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp ht
  have hl := Real.tendsto_log_atTop.comp ht
  have hr := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp ht
  filter_upwards [eventually_ge_atTop 2, hu.eventually (eventually_ge_atTop 2),
    hl.eventually (eventually_ge_atTop (32 * Real.log 2)),
    hr.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with A hA huA hlA hrA
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hAone : (1 : ℝ) < A := by exact_mod_cast (by omega : 1 < A)
  let z := uniformSieveCutoff A
  have hz2 : 2 ≤ z := Nat.le_floor huA
  have hzr : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
  have hzpos : (0 : ℝ) < z := by linarith
  have hzup : (z : ℝ) ≤ (A : ℝ) ^ (1 / 16 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hAr.le _)
  have hzlow : (A : ℝ) ^ (1 / 16 : ℝ) ≤ 2 * z := by
    have hf := Nat.lt_floor_add_one ((A : ℝ) ^ (1 / 16 : ℝ))
    change (A : ℝ) ^ (1 / 16 : ℝ) < (z : ℝ) + 1 at hf
    linarith
  have hzA : z < A := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt hAone (by norm_num : (1 / 16 : ℝ) < 1)
    rw [Real.rpow_one] at hh
    exact_mod_cast hzup.trans_lt hh
  have hlogz : Real.log (A : ℝ) ≤ 32 * Real.log (z : ℝ) := by
    change 32 * Real.log 2 ≤ Real.log (A : ℝ) at hlA
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hAr _) hzlow
    rw [Real.log_rpow hAr, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzpos.ne'] at hh
    nlinarith
  have hlogzp : Real.log (z : ℝ) ≤ Real.log (z + 1 : ℕ) :=
    Real.log_le_log hzpos (by exact_mod_cast Nat.le_add_right z 1)
  have hzpow : (z : ℝ) ^ 4 ≤ (A : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ ((A : ℝ) ^ (1 / 16 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hzup 4
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hAr.le]
        norm_num
  have hquarter : 0 < (A : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hAr _
  have hlogA : Real.log (A : ℝ) ≤ (A : ℝ) ^ (1 / 4 : ℝ) :=
    (div_le_one₀ hquarter).mp hrA.le
  exact ⟨hA, by omega, hzA, hlogz.trans
    (mul_le_mul_of_nonneg_left hlogzp (by norm_num)), hzpow, hlogA⟩

end Hindman168
