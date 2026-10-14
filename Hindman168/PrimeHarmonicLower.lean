import Hindman168.PrimeAPWindow

/-!
# A quantitative lower bound for actual dyadic prime harmonic mass

The total log mass is asymptotic to A on [A,2A). Comparing each log p
with (2A log(2A))/p yields H >= 1/(8 log A) eventually. This lower bound
is sufficient to normalize the Abel discrepancy without claiming an
unproved asymptotic formula for H itself.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology

noncomputable def primePoolLogMass (A B : ℕ) : ℝ :=
  ∑ p ∈ primePool A B, Real.log p

theorem primePoolLogMass_eq_residue (A B : ℕ) :
    primePoolLogMass A B = primePoolLogResidue 1 0 A B := by
  simp only [primePoolLogMass, primePoolLogResidue, Nat.mod_one, ite_true]

theorem primePoolLogMass_le_harmonic (A B : ℕ) :
    primePoolLogMass A B ≤ (B : ℝ) * Real.log B * primePoolHarmonicMass A B := by
  have hpoint : ∀ p ∈ primePool A B,
      Real.log p ≤ ((B : ℝ) * Real.log B) * (p : ℝ)⁻¹ := by
    intro p hp
    have hmem := primePool_mem.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hmem.2.2.pos
    have hpB : (p : ℝ) ≤ B := by exact_mod_cast hmem.2.1.le
    have hm := mul_le_mul hpB (Real.log_le_log hp0 hpB)
      hmem.2.2.log_pos.le (Nat.cast_nonneg B)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hp0).mpr
    simpa only [mul_comm] using hm
  calc
    _ ≤ ∑ p ∈ primePool A B, ((B : ℝ) * Real.log B) * (p : ℝ)⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem log_double_nat_le {A : ℕ} (hA : 2 ≤ A) :
    Real.log (2 * A : ℕ) ≤ 2 * Real.log (A : ℝ) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have h2A : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2A
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num) hAr.ne']
  linarith

theorem primePoolHarmonicMass_lower_of_log {A : ℕ} (hA : 2 ≤ A)
    (hθ : (A : ℝ) / 2 ≤ primePoolLogMass A (2 * A)) :
    1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < A))
  have hH := primePoolHarmonicMass_nonneg A (2 * A)
  have hupper : primePoolLogMass A (2 * A) ≤
      4 * (A : ℝ) * Real.log (A : ℝ) * primePoolHarmonicMass A (2 * A) := by
    calc
      _ ≤ (2 * A : ℕ) * Real.log (2 * A : ℕ) * primePoolHarmonicMass A (2 * A) :=
        primePoolLogMass_le_harmonic A (2 * A)
      _ ≤ (2 * A : ℕ) * (2 * Real.log (A : ℝ)) * primePoolHarmonicMass A (2 * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (log_double_nat_le hA)
          (Nat.cast_nonneg (2 * A))) hH
      _ = _ := by push_cast; ring
  have hc : 1 ≤ 8 * Real.log (A : ℝ) * primePoolHarmonicMass A (2 * A) := by
    apply (mul_le_mul_iff_right₀ hAr).mp
    nlinarith [hθ.trans hupper]
  apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hc

theorem primePoolLogMass_dyadic_div_tendsto :
    Tendsto (fun n : ℕ => primePoolLogMass (2 ^ n) (2 ^ (n + 1)) / (2 ^ n : ℕ))
      atTop (𝓝 1) := by
  simpa only [← primePoolLogMass_eq_residue, Nat.totient_one, Nat.cast_one, div_one] using
    primePoolLogResidue_dyadic_div_tendsto (by decide : 1 ≤ 1)
      (by decide : Nat.Coprime 0 1) (by decide : 0 < 1)

theorem primePoolHarmonicMass_dyadic_eventually_lower :
    ∀ᶠ n in atTop, 1 / (8 * Real.log (2 ^ n : ℕ)) ≤
      primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) := by
  filter_upwards [dyadic_atTop.eventually (eventually_ge_atTop 2),
    primePoolLogMass_dyadic_div_tendsto.eventually
      (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))] with n hn hθ
  have hAr : (0 : ℝ) < (2 ^ n : ℕ) := by exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  have hlog : ((2 ^ n : ℕ) : ℝ) / 2 ≤ primePoolLogMass (2 ^ n) (2 ^ (n + 1)) := by
    have ht := ((lt_div_iff₀ hAr).mp hθ).le
    linarith
  have hb := primePoolHarmonicMass_lower_of_log hn (by
    simpa only [Nat.pow_succ, Nat.mul_comm] using hlog)
  simpa only [Nat.pow_succ, Nat.mul_comm] using hb

theorem primePoolHarmonicMass_dyadic_eventually_pos :
    ∀ᶠ n in atTop, 0 < primePoolHarmonicMass (2 ^ n) (2 ^ (n + 1)) := by
  filter_upwards [dyadic_atTop.eventually (eventually_ge_atTop 2),
    primePoolHarmonicMass_dyadic_eventually_lower] with n hn hH
  have hlog : 0 < Real.log (2 ^ n : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 ^ n))
  exact lt_of_lt_of_le (one_div_pos.mpr (mul_pos (by norm_num) hlog)) hH

end Hindman168
